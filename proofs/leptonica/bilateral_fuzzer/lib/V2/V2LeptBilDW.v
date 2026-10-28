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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB LeptBracketB LeptCellsB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptUb V2LeptPixCopyST V2LeptPixMisc V2LeptPixaCreate V2LeptPixDestroyH V2LeptPixaDW V2LeptBilCW2 V2LeptBilCW3 V2LeptBilCW4 V2LeptBilD_iface V2LeptBilDRun.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2LeptBilDW () := "C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:asr_callocC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc8aic_baseC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase2ASK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase4liveK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or02C45stdpp9bitvector;definitions9bv_eq_decI47Corelib4Init6Specif7sumbool00K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or01K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6eq_decK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init9Datatypes7nat_indI47Corelib4Init5Logic2ex00C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB4cellC46Stdlib5Lists4List6nth_okC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixaDW3PA4C46Stdlib5Lists4List6in_decC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixaDW7pd_goneC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixaDW7pd_memqc5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW7fin_decC46Stdlib9micromega;ZifyClasses6eq_iffI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4lctx00I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3Cok00I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs1W00C56Stdlib6ZArith6BinInt1Z3powc5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW7bd_keepC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8sub_liveC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs5PIXatC5ARocqVerifyHarness?AgentSubmission6Common8PropExec9u64_rangeC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5w_invC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase<ai_live_hullC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface7round16C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC5ARocqVerifyHarness?AgentSubmission6Common5Hoare3at_C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase5ownedC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface8al_in_roC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface8al_in_rwC5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9blk_rangeC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_vmC4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8WalksLib8zbv_selfK46Stdlib9micromega7EnvRing5PExpr07C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecW=exW_blk_apartC5ARocqVerifyHarness?AgentSubmission6Common7StepTac6u_Z2bvC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7rdn_extC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3FRMK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase5LLU16K46Stdlib9micromega:ZMicromega;ZArithProof01I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs4pixv00C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_topC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LIVKC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5c_sp0C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6ll_imgC47Corelib4Init9Datatypes3sndC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs>sub_live_transC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots9LIVK_byteC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase9FRM_rdn16C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8FRM_monoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9FRM_transC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs;PIXat_frameC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5POSTMC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4LSTKC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8LSTK_valc5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW7bd_thruC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB8LIVK_rdnC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots4FRMxC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots5LIVKxC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots6inslotC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots>POSTD_blk_byteC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots?POSTD_rdn_aboveC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface7al_segsC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase8p16_segsC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses:impl_morphC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6ck_topC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8heap_gapC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface:al_globalsC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface=al_errno_slotC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5hcellC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs7scratchC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8blk_byteC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3inZC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3winC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots5POSTDI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixaDW=POSTD_rdn_blkC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptPixaCreate:pixa_cellsC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_img64C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ro_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_roC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_lg_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_lgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:pin_ag_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs5ll_agC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=pin_errno_imgC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_errnoC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8ll_hcellC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_hcellC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;pin_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:ll_devnullC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs<pin_ro_belowC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=above_not_gapC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs8pin_globC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9pin_errnoC47Corelib4Init9Datatypes3fstC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4c_A0C56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface6al_romK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6w_pureC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun5bl_LbC5ARocqVerifyHarness?AgentSubmission6Common5Hoare:regs_agreeC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission6Common7SeqExec6v_jalrC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs7cs_keptC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic:not_eq_symC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith6zneq_wC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs9POSTM_subC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;POSTM_transC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom6roomtrC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom<roomtr_transC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs;cs_kept_getC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun5bl_HlC5ARocqVerifyHarness?AgentSubmission6Common5Reach8rz_reachC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun5bl_HmC5ARocqVerifyHarness?AgentSubmission6Common8VmLedgerAwith_vmmaps_twiceC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase8W_free16K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00c5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW7bd_restI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSetC5ARocqVerifyHarness?AgentSubmission6Common:AllocIface;ALLOC_STACKI47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs9C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs18C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs19C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs3C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs4C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs3cs8C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs20C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs21C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs22C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs23C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs24C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs25C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs26C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs4cs27C5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bil_objC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilD_iface:bil_blocksC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB6POSTMcC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW46bw_bscC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_minvC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_maxvC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_ncC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_kxC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_kfC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_spatC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW46bw_rngC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW26bc_bl2I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_paC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_lsC47Corelib4Init9Datatypes3appC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB7cellsAtC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW26bc_blkC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptArithB6nc_valC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilSegs7kidx_okC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6set_rcC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW48bw_datasC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_parrC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW45bw_baC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW47bw_barrC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptPixaCreate9pixa_blksC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_wC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs3p_hC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW48bw_pixesC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW48bw_datadC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW36bc_memC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW49bw_linesfC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW49bil_chainK5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW44bilw01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission2V2>V2LeptLinePtrs7lp_rowsK47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List9nth_errorC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB;cellsAt_nthC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission2V2:V2LeptBase9W_sok_winC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun4bl_AC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=sub_live_reflK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptCmapArr8rinv_WP2C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9DitherLib8rinv_rdnI6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6pix_wf00C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs9pix_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs8bytes_atC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptExecW;exW_blk_rngC5ARocqVerifyHarness?AgentSubmission6Common7StoreOk9mem_growsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptSlots6slotokC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun4bl_BK46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9LeptArith6wpl_ofC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica;LeptStructs6p_dataC56Stdlib6ZArith6BinInt1Z;mul_pos_posK46Stdlib9micromega=RingMicromega5Psatz01c5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW=bd_keep_postdc5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW=bd_thru_postdc5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW9live_neq'C5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW38sub_noneC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun4bl_Cc5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW;bd_keep_rdnc5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW?pixa_cells_keepc5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW8live_neqC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixaDW9pd_staticC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixaDW6pd_memC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs6W_sub0c5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW;pd_gone_decC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun5bl_F0c5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW;live_neq_szc5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW=bd_keep_postmc5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW=bd_thru_postmC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun5bl_F1C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun5bl_F2C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun5bl_F3C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun5bl_F4C5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun4bl_GC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs:POSTM_reflC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptRoom;roomtr_reflC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun4bl_IC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun4bl_JC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptBilDRun4bl_KC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB6rinv_WC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8LeptDefs=cs_kept_introC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica<LeptBracketB5LIVKcc5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW>FRM_byte_abovec5ARocqVerifyHarness?AgentSubmission2V2;V2LeptBilDW:bld_loop_WC5ARocqVerifyHarness?AgentSubmission2V2<V2LeptPixaDW?pixaDestroy10_WC5ARocqVerifyHarness?AgentSubmission2V2AV2LeptPixDestroyHApixDestroy_free_WC5ARocqVerifyHarness?AgentSubmission2V2=V2LeptPixMisc@pixDestroy_dec_WC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilD_ifaceIbilateralDestroy_contractC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPixCopyTR3hdvC5ARocqVerifyHarness?AgentSubmission2V2?V2LeptPixCopyST3hdvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7seg_romC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica:LeptCellsB5c_offC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9DitherLib4rinvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica9DitherLib5inregK46Stdlib9micromega=RingMicromega5Psatz05I5ARocqVerifyHarness?AgentSubmission2V2<V2LeptBilCW44bilw00C5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilD_iface6BD_WINC5ARocqVerifyHarness?AgentSubmission2V2@V2LeptBilD_ifaceCPC_bilateralDestroy".
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Section BilDW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition bd_rest : list (bv 5) := [3; 4; 8; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma live_neq : forall (A0 : AS) (q q' : word) k, live A0 q = Some k -> live A0 q' = None -> q <> q'.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilDW ()) ["BilDW"] "p'0h01Lh11Hh21qh32A0h41Fh51eh61kh71oi001oh82q'p;3p;2p;1p;4p;6p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p70R1g001>R0p4p710R2p8P1g001ZR1p4p710R3p8p10028p4p70R4P2p8P4P3p8p1002fp4p7210P3p8p1003Rp4p70R4P2p8P4P3p8g004Hj3>Tg005Qj3=Tg006Zj26Tg007[j11Tg008@j1<Tg008^j18Tg009AR3j17Tg009cj42Tg00:fj23Tg00;Hj30Tg00;bj15TP0j64Tg00<Dj29TP1j7;Tg00<cj1:Tp,2ALR1p,2CLR0p,3ASR9>105=1R0'6g00=<#1#1#1#1#1#1#<#8R4g00=aR2%72R5P1P0f3R6f2R7C2f0R8,3230P1P0f4R9P7C2%52R:505A0496R;P4P9P1P0f7R<P8C21329R=505g00>?R>]0X24P1P0f6P9C21326505P5P1P0P<f5R<C2132<R09058X75P8P:P7E4A05:=P5P:P3P2p-0P8P>g00>\n10110000021000000X55g00?8P0P8E4P>19>8b1b0W0P<P8P7F;W1%:;eW4W0W6X84W2W3o"). Qed.
Lemma live_neq' : forall (A0 : AS) (q q' : word) k, live A0 q = Some k -> live A0 q' = None -> q' <> q.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilDW ()) ["BilDW"] "p'0h01Lh11Hh21qh32A0h41Fh51eh61kh71oi001oh82q'p;3p;2p;1p;4p;6p;7g004Hj3>Tg005Qj3=Tg006Zj26Tg007[j11Tg008@j1<Tg008^j18Tg009AR0j17Tg009cj42Tg00:fj23Tg00;Hj30Tg00;bj15Tg001>j64j7;Tg00<Dj29Tg00<cj1:Tp,2ALR1p,2CLR2p,3ASR9>125=1R2'6g00=<#1#1#1#1#1#1#<#8R3g00=aR4%74R5P1P2f3R6f2R7C2f0R8,3430P1P2f4R9P7C2%54R:505A0369R;P3P9P1P2f7R<P8C21349R=505g00>?R>]0X23P1P2f6P9C21346505P5P1P2P<f5R<C2134<R29058X75P8P:P7E4A05:=P5P:P0P4p-0P8P>g00>\n10110000021000000X55g00?8P2P8E4P>19>8b1b0W0P<P8P7F;W1%:;eW4W0W6X83W2W3o"). Qed.
Lemma live_neq_sz : forall (A0 : AS) (q q' : word) k k', live A0 q = Some k -> live A0 q' = Some k' -> k <> k' -> q <> q'.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilDW ()) ["BilDW"] "p'0h01Lh11Hh21qh32A0h41Eh52L'h62NEh71eh81kh92k'h:1oi001oh;2q'i011zp;3p;2p;1p;4p;6p;7g004Hj3>Tg005Qj3=Tg006Zj26Tg007[j11Tg008@j1<Tg008^j18Tg009AR0j17Tg009cj42Tg00:fj23Tg00;Hj30Tg00<cj14Tg001>j65Tg00?Tj69Tg00@1j4;Tg001Zj7:Tp,2ALR1p,2CLR2p,3ASR9>125=1R2'6g00=<#1#1#1#1#1#1#<#8R3g00=aR4%74R5P1P2f4f3R6C2f1,34R730P1P2f5R8P6C2=057f29046#4f6R7=038R9P3P7P1P2f9R:f0R;C21347R<505g00>?]0X23P1P2f8R=P7C21348R>505P5P1P2P:f7R2C21342R1905;X:5P;P>P6E5A05><P5P4P0P4P4P;P;P2n10110000021010100X75P<P1P;E9A0472A042=P8P4P=P:P;C;O1W4P;O1b1b0W0P2P;P6F:W1%49eW6W5W0X94W8X;3W2W3o"). Qed.

(* [comment removed for export] *)
Lemma fin_dec : forall (f : Z -> Z) (n : nat) (lo : Z) (q : word),
  (exists k, (lo <= k < lo + Z.of_nat n)%Z /\ q = Z_to_bv 64 (f k)) \/ (forall k, (lo <= k < lo + Z.of_nat n)%Z -> q <> Z_to_bv 64 (f k)).
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilDW ()) ["BilDW"] "p'0h01kh14__x1h24__x2h32Hkh47__arithh54__ffh68__varmaph75__with84__x3h91ni001nh:1qh;1xi011xh<4cstrh=2loh>1Hh?3Hk0h@4__p1hA1ei021ehB1EhC2IHhD2NEhE2NKhF1RhG1dhH1fhI1mhJ1ohK1si031shL1yp;1p;2p;4p;6p;3p;7p;<p;Bp;8g007[j1ETg008@j1~Tg008^j1kTg00@Mj26Tg00@ij21Tg00AOR0j2@Tg00AiR1j14Tg00BIR2j20Tg00BfR3j23Tg00CBR4j22Tg00C]j1FTg00D;j4qTg00D^j2LTg00E8j6NTg00Eaj4_Tg00FHj1fTg00Fhj1dTg00GHj2WTg00Gfj1cTg00HDj4VTg00Hbj1bTg00I@j1aTg00Ikj2OTg00JNj2UTg00;bj1`Tg00K1j6|Tg00KUj2{Tg00L7j2xTg00;Hj38Tg00Lcj3wTg00MBj4tTg00N4j3^Tg00NNj3sTg00<cj1>Tg00O6R5j2]Tg00OVR6j1;Tg00P5j1pTg00PSj1QTg00Q8j4[Tg00Qcj4YTg00R>j4ZTg00RXj3XTg001Zj6lj7jTg00S2j1nTg00SWj2oTg00T7j4STg00Tbj6iTg00UFj4hTg00UgR7j2rTg00VAl<TTg00VflBgTg00WLl<uTg00X1j7vTg00XUj3eTg00Y8j7yTg00Y\j8zTf1R8f0R9#4'0p=}f2R:1389'2p=Af3R;A8:89'2p=9g00=aR</r9p=5118998;:#>p==A8:89#>p=B1L<9p=:g00Z@R=P<P<P<P1P1P;P:P8g00Z_R>g00[>R?P9M<Tp=mP<P<P<P<P<P<P2P9P8P:P2P;f4R2f5R@f6RAf7RBf8RCf9RDMBgp=MP<P<P3PBP3PAP@P2P;P:P8P9M<up=JP<P8g00[\P9CSp=IP8g00\CR3g00\bREPEg00]BRFP9g00]bFvp=<Ae<89p=?P<P8g00^BP9CSp=HP:P3PEPEPFP8P9Fyp=KP;P3PEPEPFP:P8P9Gzp=G118998;:p=C16:8/29p=\162;%49,08,3:'2p=7P=P=P<P<P6P1P1P;g00^iP:P8P9M<Tp=RP=P<P<P<P1P1P@P2P;P:P8P9M<Tp=P162;1089,3:'2p=DP<\<g00=<R1#ER6#E#E#E#E#E#~RG#kRH16:9RI1}:;7A9RJPHP8P@P9O1,1GC9X0<#5PHP:PGPAP8O1C=\J^0<'@]:^=<RJX9=%4>R>,0:9AI9RIPHP8P2P9O1,1GC9X0<#5P@P8O1,1GRK9BH:\I^0<16;8RL10;>RM,38RN'210;?9AL8ROPLPNPLP9X;<RNP?O1RP,0;RQ,38%FLPN1389#FXL<X;<RLP8P8%:8PMPQPNPNPNP<P<g00_M1089Cq#:XI<X9<RQP;P;%:;P>PPPNPN%49#:X;=RP1L<?CmM:MGJENP9C_POp-0ROg00`1R>#fRM%d>R>P<1W<:RRP8%c<CVRS%b<RT%a<RU1O<1RV1O<6R6'I,<URW1U<?RX,?V,H6,<U5KU%`ERYPUP3PEPEPFP2E|CG1{UFRZP9P:g00`]R[g00a=R\'L1x9:=8[\dAw<?8CtR\b5b6b7X1<X2<W@1698R[109?7A8P;[^1<^2<^@OP9PBP;O1,1GRO9BH2P;P@P8O4b4b?X3IX0<3^X:HX=<AsG9KA8H9KRK%>K']P5PHP8PGPAP:O1CCRK%>K%;ARK#4RI,02R],399\29R^PHP;PCP9O1,1GC9X0<#5PHP2PGPDP8O1C=\^^0<'@P9A8H:OROPHPCP2O1,1GR^PAP9P9PA%;CD7R_PHP8f:R`P9O1,1GRaC9X0<#5f;RbP8O1,1GRc9BH:\_^0<'@X:HP@P9P9P@%;BD7R_PHPDP@O1,1GPDP9O1,1GRdC9X0<Re#5P`PAO1,1GP`P8O1,1GRf5BH\_^0<P<PeP21622Re132]R_'2RgA8H^^Pg%4ARg%p1Rh'0Ri,02Rj,32Rk,2ePeP_PePk%FePNPLP2P2%:2ReP]PjPNPNPNPQP2P2PePIPiPNPNPPPKPi109hRiX;<RKPAPg%:gCREPM:MGJEN%QA16?gPMP>PSPTPU1IX6,<UPY1IVV,<U1U<hRX,?6,?V,HV,<U5KUCGPZP\b5b6b7X1<X2<16?8P8P8P8P810:hRSDD[^1<^2<P9%4CRgPAP8O3b4b<C[1LH^CYCZ3XP;P9ElWAP9O1%>OP@102hP;O210@hROP9P9POPBD7ROPHP2PdC9X0<#5ABH@f\O^0<'@P010AhR0P9P9P0PgDDRgPHP@PaC9X0<#5ABHAc\g^0<PBP9P9PB%;DD7RgPHPAPGPbP9O1CCRA'2X0<#5PHPBPGf<RcP8O1C=Ra\g^0<'@P910BhRgP9P9PgPDD7Rg/2AX0<#5P7P<10ChR7P9P9P7P`D7PHPBPGPcP9O1CCR7'2X0<PDP9P9PD%;bD7RAPHPCf=R0P9O1,1GC9X0<#5PHPDPGf>ROP8O1C=\A^0<'@P910`hRAP9P9PAPcD7PHPDPOP9O1,1GC9P410bhR4P8P8P4P0D7PHP`PGf?R4P8O1CCP0P9P9P0%;4D7RAPHPcfARfP9O1,1GC9X0<#5PHP0PGfBRdP8O1C=R^\A^0<'@P9100hRIP;P;PI%44RIDDPHP0PGPdP2O1CCf@RjP9P9Pj%;dD7RdPHP4fDP9O1,1GC9X0<R]#5PHPjPGfEP8O1C=\d^0<P<P]P@164@R]%;fRd#4Rj,04Rk,3@R_'2RlPHPOPGfCRmP@O1CCPl%4fRl/0hRn,04Ro,3@Rp,2]P]P_P]Pp%F]PNPLP@P@%:@PkPoPNPNPNPQP4P4%:4PjPnPNPNPPPdPnPKPfPl%:lCREPM:MGJEN%Qf16?lPMP>P<PRP81W<;CVRRPTPU1?VXRn/I6,<U%n1,O<R1,?n,H6,<U5KURnPY1?1X,?V,H6,<U9KUWRWCGPZP\b5b6b7X1<X2<X8<PiP8P8PiP:DDP8P:P:P810;hDD[^1<^2<^8<P9%4mPBPfP;O4b4b<C[P9CYCZ3XWBW3P8P9O2n2001000000121000000W>X0<P8P9O2n2001000000121101000W>P9O1Pa\g^0<PCP9P9PC%;`D7Rg/27X0<#5PHPCPGP0P8O1C=\g^0<1o8DA8<8DR0%>0']P5A8<:`R5%>5PHP`PGP4P;O1C=P9A8<;bRbP<PcP^^3AX0<%;ORA#4R^,0cRG,3c9\ccPDW3P2P9P;FjWAP9O1%>bP@P216c2R@132GRb'2%4ORD/0h,0c9A@2RhP@PbP@PNPKPDO1RbO1R`,0cR5,32%F@PNPLP2P2PePGP5PNPNPNPQPcPc%:cP^P`PNPNPPPAPbPKPOPD%:DCREPM:MGJENP;C_Ph%Q416?IPMP>PRPTPUPWPYPUPUP3PEPEPFP<P6g00a]PVCS,<UEiPYPnCGCGPZP\b5b6b7X1<X2<X8<109S9A[8A8<:8g00>?[PSP;P;PSP2DD[[^1<^2<^8<P9PlPBP4P:P;O5b4b<b?O2WEP9O1n200110300021010211100bKX3gX0<3^WFP9O1n200100000021100011000bJWDP9O1n200110300021110211100bGX:HX=<XCJX9=P9ChX9=WHo"). Qed.

Lemma pd_gone_dec : forall pa parr ba barr (pixes datad : Z -> Z) (q : word),
  pd_gone pa parr ba barr pixes datad q \/ ~ pd_gone pa parr ba barr pixes datad q.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilDW ()) ["BilDW"] "p'0h01kh11Hh21Eh34__x1h42Hkh51ii001ih61xi011xh71Ih87__arithh94__ffh:8__varmaph;5__with<1oh=3Hk0h>2NIh?2R1h@2R2hA2bahB4barrhC5datadhD1mhE1ni021nhF2pahG4parrhH5pixeshI1qhJ1si031shK1yp;1p;4p;3p;2p;7p;5p;6p;<p;Bp;8p100bDp4p70p100cIp4p710p8g007[j1;Tg008@j1qTg008^j1^Tg00NNj1[Tg00cdj4:Tg00d\j4hTg00e7j39Tg00<cj11Tg00O6R0j2]Tg00eNj75Tg00AOR1j22Tg00S2j1XTg00P5j1VTg00fJj5?Tg00RXj3@Tg00gFj4JTg00@Mj2ATg00AiR2j1NTg00BIR3j2DTg00@ij27Tg00CBR4j28Tg00BfR5j2<Tg00D^j26Tg00;Hj3>Tg00hAj3ITg00C]j1\Tg00D;j4ZTg00E8j6PTg00Eaj4WTg00FHj1UTg00Fhj1TTg00GHj2STg00Hbj1pTg00I@j1oTg00JNj2RTg00Ikj2nTg00T7j4FTg00XUj3lTg00;bj1kTg00KUj2gTg00L7j2fTg00Lcj3eTg00MBj4dTg00Qcj4MTg00R>j4LTg00N4j3CTg00Q8j4cTg00OVj1KTg00UgR6j2bTg00VAl<aTg00VflB`Tg00WLl<iTg00X1j7jTg00Y8j7_Tg00Y\j8mTf0R7#K#Kp=Bf2R8f1R9/<7'8p=4f3R:A>897'8p=3g00=aR;/b7p==17979>:8p=0g00Z@R<P;P;P;P2P2f5R2f4R=P:P8P9P7M<ap=YP;P;P;P;P;P;P3f7R>f6R?P2P3P=g00[>R3P3P:P8P9P7MB`p=HP;P;P5P>P5P?P2P=P:P8P9P7M<ip=GP9g00\CR5g00\bR@P@g00]BRAP7g00]bFjp=EP8P5P@P@PAP9P7F_p=QP:P5P@P@PAP8P9P7Gmp=OP;\;R5g00=<RB#;RC#;#;#;#;#;#qRD#^REPE%[DP7P?P2P=P:C:RFChA9E7FRF%1F']P0P>P?P2P=C:99E9R0%10f8R0P>P?P2P=P:P8F5RF%1F'2P7P0P>P?P2C:99E8RFf9RGP0P>P?P2P=P:F5RH%1HPGP0P>P?C:99E:P2P=P3%XC#;#VRCP:D?;@73@W7P7O1%1FP2g00Z_#B#B#B#B#BRFP3P:CJ1A37RH%NFRI,D3RJ747RKPEP=P?P7O1,7DC3X0;#=PEP2PDP>P9O1C0#1\K^0;'2P1PKPEP2P>P7O1,7DC3X0;#=PEP?PDP0P9O1C0#1\K^0;f;RLf:RMPGP0P>P?P2F5RN%1N'2P7PKPEP?P0P7O1,7DRNC3X0;#=P6P;PKPEP>PGP7O1RO,7DRPC3X0;f=RQf<RRPLPMPGP0P>F5RS%1S'2P7PKPEPGPLP7O1,7DRSC3P41A39RT?49JRUPEPMPDPRP9O1C0fARVf@RWf?RXf>RYPQPRPLF5RZ%1Z'2P71A3:RZ?4:JR[PEPQPDPXP=O1C0fDR\fCR]fBR^PVPWPXPYF5R_%1_R`P\P]P^PVC:99EYPWPXP3PCPYD?P;A4H7CRaPEPXPDPVP7O1C0PEPXPDPWP7O1C0'2'8RbX5;P21A32Rc?42CRdPEPYPDPWP2O1C0RePEPYPDPXP2O1C0Rf'21<2JRg,8c1D3CRh94c2RiPcPgPcP7X6;RgPCO1Rj,D3Rk,<2p-0Rl/6cA>lcce9IccPg1<97#\XK;X6;RcP2P216;2PJPkPgPgPgP;P;g00_M1D97CZ,6;XD;XE;Rk16;3RmPIPjPgPg%N7,6;X6<PFPC16;CEYR<GHGGEPP9CWPig00`1Ri#URj%TiRi1S;9Rn%p;Ro%o;RpP;1R;3Rqg00[\1n;BRBCF,EpRrP;PBg00^BRs1R;CRt9l;qCF,Ep5QpRq%k@R@P;PBPsPtCF,Ep9QprRrCO1gpARAP7P8g00`]Rtg00a=Rs'61f78=>tsdAe;39CdRsb9b:b;X3;A4H7hA4T9CRH[^3;P7P>P9O2b8b=RtA@ef7CMCL3C3@W2W4P9P7O2n2001000000121000000W1X0;P9P7O2n2001000000121101000W1P7O1PGP9O1,7DRf9>E>#1\K^0;P>PFP3P?CJPKPEP>PNC3X0;#=A>E0f#1\K^0;'2P1PKPEP0PPC3X0;#=PEPGPDPMP9O1C0#1\K^0;PYPQPRPLPMPGP0F5RP%1P'2P7PKPEPGPMP7O1,7DC3X0;#=P6P;PKPEPMPSC3X0;PWPXPYPQPRPLPMF5RS%1S'2P7PKPEPRPQP7O1,7DC3P4PUPEPQPDPYP9O1C012_`P7PEPWPDPVP=O1C0fGR`fFR_fERUP\P]P^PVF5RS%1SP`P_PUP\C:99EVP]P^P3PCPVD?P;PEP^PDP\P7O1C0PEP^PDP]P7O1C0'2,8aX5;P2PdPEPVPDP]P2O1C0RdPEPVPDP^P2O1C0RS'2PtACdS7CMCL3C3@W2X4[P9P7O2n2001000000121000000W1X0;P9P7O2n2001000000121101000W1P7O1PEPMPDPLP9O1C0#1\K^0;PXPYPQPRPLPMPGF5RG%1GRKP1PWPXPYPQC:99EMPRPLP3PCPMD?g00>?RMP7PVPWPXPYC:99ELPOW7P7O1PQPRP3PCPLD?P6P;PEPQPDPXP7O1C0PEPQPDPYP7O1C0'2,8aX5;PMP7P4PHPEPWPDP^P9O1C0PEPWPDPVP9O1C0'2PMP7A4Z:CPEP]PDPUP=O1C0PEP]PDP\P=O1C0'2P1PEP\PDP_P2O1C0PEP\PDPUP2O1C0PMP7PEPUPDP`P?O1C0PWP>1A3>R31<>JRW'81<>hR`,83P3PWP3P`16l39I33PgPcP>P>16;>PJPhPgPgPgPkPmPIPCP<GHGGEPPjPiPnPoPpPrP@PqCOPAPsb9b:b;X3;A4T9h\a^3;P7P0P=O2b8CcR=P7O3W2P7O1PEPUPDP_P?O1C0PQP>P=P7O3W2P7O1n200100000021100011000W1W4P9P7O2n2001000000121000000X1bX0;P9P7O2n2001000000121101000W1P7O1n200100000021000011000X1GPKe3CW@P7O1n200100000021100011000b<W?P7O1n200100000021100011000b<W>P7O1n200110300021010011102bJWIXC5WHXB;XA;XG;XF;o"). Qed.

(* [comment removed for export] *)
Definition bd_keep (C : lctx) (A Ak : AS) (m M1 mk : word -> option byte) (s bil pixs : Z) (v : pixv) : Prop :=
  sub_live Ak A /\ live Ak (Z_to_bv 64 pixs) = Some 64%Z /\
  (forall (q : word) k (x : word), live Ak q = Some k -> q <> Z_to_bv 64 bil -> (u q <= u x < u q + k)%Z -> ~ (pixs + 20 <= u x < pixs + 24)%Z -> mk x = m x) /\
  (forall a, (s - 48 <= a)%Z -> (a + 8 <= s)%Z -> rdn SEGS mk (Z_to_bv 64 a) 8 = rdn SEGS M1 (Z_to_bv 64 a) 8) /\
  FRM C s m mk /\ PIXat mk pixs v.

(* [comment removed for export] *)
Definition bd_thru (mk m : word -> option byte) (bil : Z) : Prop :=
  forall a nn, (bil + 16 <= a)%Z -> (a + Z.of_nat nn <= bil + 88 \/ bil + 96 <= a /\ a + Z.of_nat nn <= bil + 104)%Z ->
  rdn SEGS mk (Z_to_bv 64 a) nn = rdn SEGS m (Z_to_bv 64 a) nn.

(* [comment removed for export] *)
Lemma bd_keep_rdn : forall C A Ak m M1 mk md (s bil pixs : Z) v (q : word) k (a : Z) nn,
  Cok C -> W C A m md -> live A (Z_to_bv 64 pixs) = Some 64%Z -> (0 <= pixs < 2 ^ 64)%Z ->
  bd_keep C A Ak m M1 mk s bil pixs v -> live Ak q = Some k -> q <> Z_to_bv 64 bil -> q <> Z_to_bv 64 pixs ->
  (u q <= a)%Z -> (a + Z.of_nat nn <= u q + k)%Z -> rdn SEGS mk (Z_to_bv 64 a) nn = rdn SEGS m (Z_to_bv 64 a) nn.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilDW ()) ["BilDW"] "p'0h04__x1h11xh24__x2h34__x3h44H2a0h57__arithh67__sat17h77__sat18h84__x4h94cstrh:4__ffh;8__varmaph<5__with=4__x5h>4__x6h?1ah@1khA1qhB1HhC3H2ahD4__p1hE1ihF2HahG3Hx0hH2_HhI1mhJ4pixshK1yhL1zhM1AhN3APqhO3ATLhP2AkhQ1ChR2CKhS2GqhT3H1ahU2HWhV3Hk0hW2HxhX4KEEPhY5LpixshZ2Lqh[3LqAh\4LqA'h]2M1h^2Nph_3Np'h`2Nqha2Rphb2Rqhc3SUBhd4TOPqhe1Xhf3_H0hg2a0hh1bhi3bilhj2mdhk2mkhl1ni001nhm2nnhn3nn'ho1shp1vp%0p&0p;3p;2p;1p;5p;8p;:p;9p;4p;?p;6p;Ep;7p;<p;Bg004Hk30jTg00hgk30iTg005Qk30VTg006Zk20JTg007[j1PTg008@k109Tg008^k107Tg009Aj1pTg00ilk50NTg00k0k80ITg00@ij24Tg00P5j1ETg00l2k20ZTg00BfR0j2BTg00CBS00j2>Tg00lOm:0YTg00mJk508Tg00nQj22Tg00S2j1qTg00<cj1ATg00;Hj36Tg00o;j2XTg00@MR1j20Tg00BIR2j21Tg00Fhk100Tg00OVR3j1?Tg00oXj3^Tg00AiR4j15Tg010_k10^Tg011]j1zTg012Tm90\Tg013Xm90[Tg014cj2yTg015Cj1cTg016Aj1MTg0179j2wTg017nj4vTg00;bk10:Tg0192j2uTg01:1j2tTg01;0j4[Tg00D^j2sTg00C]j1rTg00D;k40XTg00Eaj4UTg00PSj1oTg01;hk20UTg01<Pk30TTg01=4k206Tg00FHk10STg00Gfk10QTg00Hbk10PTg00I@k10OTg00JNk203Tg00Ikk202Tg00KUk20MTg00L7k20LTg00Lck30KTg00MBk401Tg01=]m?0HTg01>ej4`Tg01?hk10FTg01@cj1|Tg001Zj6jTg00@1k40ETg01Ajk30DTg01BMmE0CTg00AOj2iTg00K1k60BTg00Q8k40ATg01CZk30RTg00E8k605Tg01DTk70@Tg00:fk20WTg009ck40hTg01EPk80gTg00VAm<0?Tg00VfmB0fTg00WLm<0;Tg01FRk30eTg01G;k20bTg01Ggj3{Tg00GHk20aTg00HDk40`Tg00XUk30_Tg00T7j4fTg00X1j7eTg00Y\j8gTg00Y8k70cTg01HGk70]Tg00Tbk60dTf0R5#P#Pp=]g00=aR600W5p=Gf5R7f4R8f3R9f2R:f1R;H0h;65p=8g00[>R</05p=;A6:;5#Ap==108911;5,B:'>p=n11;5,B:p=Q119:/0;/>5p=If6R=g01HkR>P7P8P9C[P>P:P;P5C[36p=JP=P7P8g01J=S01P9P:P;P5L0gp=\1>;5,>:p=@12:;/15p=H11:;/05p=3P>P:P;P5C[p>0>P>P9P:P;C[=685p>0=P>P:P;P5C[9689p>0<1B;5,>:p=OA665<p=x1s65p=<g00Z@R?P?P6P6P3P4P4P9g00^iP:P;P5N<0?p=bP?P6P6P6P4P4P7P8P9P:P;P5N<0?p=LP6P6P6P6P6P6P2P5P;P:P2P9P8P7P=f7R2f8R4f9R3NB0fp=KP6P6P1P2P1P=P7P8P9P:P;P5N<0;p=Z20665p=SB0e6;5p=9g01K5-0b5p=Dg00`1R1?{;5p=m20a65p=WP6P:P;P5H0`p=F20265p=Y20365p=_B0_6;5p=7P:g00\CR@g00\bRAPAg00]BRBP6P;g00[\RCP5Cfg00]bRDFep=:P:P@PAPAPBP6P;g00^BREP5CfPDFep=NP9P@PAPAPBP:P;P5Ggp=aP7P@PAPAPBP8P@PAPAPBP6P9PCP:CfPDFeP;P5Ggp=C10:;/>5p>0GP:P@PAPAPBP;P5K0cp=RA{1;59{1:p=VP:P@PAPAPBP;P5K0]p=hP6P;g00a]P5Cfp=lP;P@PAPAPBP5PDFep=kP;P@PAPAPBP5J0dp=dP6P;PEP5Cfp=~P8P@PAPAPBP9P@PAPAPBP:PDFeP;P5Ggp=}P=P@PAPAPBP7P8P9P@PAPAPBP:P;P5GgGgp=TP6P6P0P2P0P=P7P8P9P:P;P5N<0;p>04p,2ALR0p,2CLRDp,3ASR:0j0DRE40iB0V0DERC-0J0S02Q02g00=<RF#PRG#PRH#PRI#PRJ#]S03$09RK$07RL&09I$07RM#pRN[S04Q04Q04g01Kag01LWP0PDPEQ01f>ROI0NP0PDPEQ01f?RPPOf<RQP3L0I%p6RRP0PCPP14K2Q03#ERS#GRTE8%;4%EGRU00ZSRV,B4S05'>fBRWfARXf@RYPPPOf=RZf;R[f:R\P3P4N:0YQ00P0PDPEPXPWI08PRP0PCPX14K\PTE8PRP0PCfDR]P:%G;R^E814KP9=L912K8R_12K:R`P`P_P9DnR_PY%qGR`#]#ERa12K9Rb%qFS06#PS07#]Rc#ERd9QbYCI#AfEReP8O1fGRfP8O156N[[[[^1L^@6^AL%Pc#ERc,XZ/05%EI,1;RI/0O&00M#pRgPX14K:Rhg00Z_Ri#?Rj#?Rk#?Rl#?S08#?S09#?S0:#?S0;#?RmPWPhPmFJ[[^?6P0PDPEfCRnPQPYPOF\A^O\33@3@PRP0PCPWP3%G4E814KZRo9=L\A=L[o12KQ/0\%5\RpAHKZQ53[PgP]14KQRqP[fFRrPqP[FJ[[[[[P5P0PDPEPnP]I08PRP0PCP]PoPTE8PRP0PCPfP:P^E814KW9=L9PnPaPbAQbndCI#AfHRoP8O1fJRqP8O156N[\_[[^1L^@6^AL1XYc/0510IXPgP]PhPmB0>ehmRsI0=[[^?6P0PDPEPrPPPnPXF\A^XZQ3@3@Q00PRP0PCPe14KOPTE8PRP0PCPoP:P^E814Kn9=L9P]PaPbAQb]dCI#AfIRtP8O1fKRuP8O156N[\_[[^1L^@6^AL1XXc/0510IWPgPsPrPhPmI0<[[^?6P0PDPEPfPYP]PWF\A^WOZ'>3@PRP0PCPrPZ%GQE814KXRs9=LOA=LPs12KY/0O%5OS0<AHKXY53PPgPo14KYRsPPPqPsPPFJ[[[[[P5PRP0PCPfPsPTE8PRP0PCPuP:P^E814Kr9=L9PfPaPbAQbfdCI#AfLRTP8O1fNRsP8O156N[\_[[^1L^@6^AL1X]c/0510IePgPoPhPmB0>thmRvI0=[[^?6P0PDPEPqPnPfPeF\A^eXY'>3@Q00PRP0PCPTP:P^E814Kf9=L9PoPaPbAQbodCI#AfMRwP8O1fORxP8O1Ry56N[\_[[^1L^@6^AL1Xec/0510IrPgPvPqPhPmI0<[[^?6P0PDPEPuP]PoPrF\A^rWX3@PRP0PCPqPX%GYE814KeRv9=LWA=Lnv12K]/0W%5WS0=AHKe]53nPgPT14K]RWPnPsPWPnFJ[[[[[P5PRP0PCPsP:P^E814Kt9=L9PqPaPbAQbqdCI#AfQRbP8O196Ny[\_[[^1L^@6^AL1Xoc/0510ItPgPTPhPmPwPhPmFJ[[^?6P0PDPEPsPfPuPtF\A^te]3@PRP0PCPwP]%GnE814KoRn9=LeA=Lrn12Kf/0e%5eAHKof53rPOPtPoP8O3PRP0PCfSRfPt%GoE8&0^q12KqRn#;?OnVP0PCfUS0>PffPRn#zRmPuPqP0PDPEQ01fVRhQ0>PfPnPrN90\P;N90[%;q12KuRr%EJRJ'y#xPr%cq%Mm%;5Rm%cuRr7O5P0PCfWS0?1ww;RICvQ0>PIO1&0:MRM5=N1u0I#A1t0I#A'>3@[^E6CI3@Q00%;u12KTRI/yJ#x%zb#M93Ir%cT9Om5P0PCfXRI1ws;RrCvPhPrO1==NM1u0r#A1t0r#A'>3@[^E63@PgPf14KuRrPqQ0>PrPqFJP5%;w12KxRq/yJ#x%csfTS0@#z#M53q%cx9Om5P0PCf[Rq1wb;RJCvfYRrPJO1==NM1u0J#A1t0J#A'>3@[^E63@P?%55RJAHKbn53xPgPI14KnRMP;fZRcPMP;FJ]CPw%5iAHKnx53sP>Pr14KxPiC[,sgWC%?5#5fRRw=HKb53nP0PDPEQ01p,4PINSf^S0Af]RnPqPIPfPwPxPsP3%?;Rs#5Rx,1bRM12KfS0B/1wRw'0%5;R_%EFRy'1=3bwR^P5X16RW10;5#rXK6X16S0CPMPW115yX16RMP_O1RvO1Rz,1bPWPWPWP6P6g00_M11;5H0X#<XI6Xl6R{PbPb%<bPxPzPWPW%<JX1?RJPsPvPMP;P_%<_CbELM:KPwPw%<wGZP5CUP^%o:%5:#;20UUSR^1B<U%;SS0D1B<V[[R_%;URvg00>\RsB0TUS;UWFRz%;V\s^FvRv%SlS0E%SkS0F%SjS0G2066iS0H'9S0I'9S0J'9#D&0S1Ri'm&001R1%W9S0K&0Q6Rj7F8%W8S0L?F:jS0M7F;&0P6Rk&0O6RlPl2036<Rs%Y`R`&0:ARxPlPl%YHRH%_yRb,7`'7Q06#YR|2026FRF'7PxPlA:l|HS0NPxANlsFCaECEC20MlBR}P5P:g00`]S0Og00a=R~'sS0PQ0O20L5:;6~dB0K6<;S0OH01R~b:b;b<X06X26X36X86%;9S0Q118y11:;53910981B<9[[[^06^26^36^86P5%5=Ph12KIQ0?P9P8PYO7b5b6b7b9b4N?0HQ03#]#]#]#ERYQ0BP0PDPEQ0AC`#M,0w40GQ00Q0@,2KRw,0YP0PDPEf_R<C`#M93wfPgPq14KfRf%?9RgPnPfPgFJP512Kh,0YQ0?,2KP0PDPEfbRgC`#M73hP0PDPEfcRfC`Rw$0F%Mwg01M_'BPLPrPRP0PCfdS0@P5%GrE8XhLPP12Kr,4KRw%|rEjPRP0PCPfPw%GIE8f\RI12Kc566RwP]P612KqR]14K596LIXJ6PL14K]Pq%|qH0EPnP5EjO1We%AwRwePwP0PDPEQ01ffS01feS00Pff`RwPnP]PSPcQ0?PhQ0>P;P5%?3S0>#5S0?,1rS0B11]cRh'0%53RC/1y=3rhRRPWQ0CQ0BPWPMPCO1S0BO1S03,1rPWPWPWP{PrPr%<rQ0?Q03PWPWPJQ0>Q0BPMP3PC%<CCbELM:KPhPh%<hGZP4CUS0BPR%o\S0>%;pRCP^P_PzPvPiP1%W;S03PkPlA:lsFS0?%_U>0D6KRU9NlFS0R5RlS0SPxQ0SCaP}P~b:b;b<X06S0SAOm5V%;;S0T?O;V[^06S0UP5PgPrO2b5b6b7b9b4Q0BPRQ0>PCP^P_PzPvQ0SQ0UP512KwPeO2b5b6b7b9b4Q0BPRQ0>PCP^P_PzPvPiP1PjPk%_SRr9:lsP}P~b:b;b<Q0DP5b5b6b7b9b4Q0BPRQ0>PCP^P_PzPvPiP1Q03PkPlQ0?PxQ0?CaP}P~b:b;b<X06Q0T\m^06P5P<PXO2b5b6b7b9b4NE0CA3nS]10hn'iP>%?\R>PgQ0@14KcS0TP6Pc%?[#5S03=35VXL6%5>Rh,1cR]/0V11pyRX,1cRm/0VPWQ0CP]PmPWPWPWP{PcPc%<cRCPhPXPWPWPJP>PXPMP\Pp%<pCbRXELM:KPVPV%<VGZAHKIqRR,0]10mRRmPWQ0CP]PWPMPpO1RpO1R],1cPWPWPWP{PcPcPCPhP]PWPWPJP>PpPXELM:KPRPR%<RGZP3CUS0>Pm%o[S0B%5[#;S0DP^P_PzPvp-0RRQ0:#SRXQ0EQ0FQ0H'9S0F'9'9S0E#DQ09#SRpQ0I'9,9XS09#DR>1m>i3VP1Q0L%W=S0:7F:%W7S0L?F9j7F;S0UPkPlPl%YGRG/7b,7FRj17H`R>PxPl17|r=:lHA:l>|5hlPxPl1l|H,kl,dlPxPlPlQ07#YR]/~UPxPlPlP>P]PxPlPlP@PAPAPBP4J0BRBANl|U5RlPxA:ljUCaECD}FTECP}P~b:b;b<X06X26X36X86X=6X>6WD11;y1198Rj535A39S8A3879'iRAA6687g00>?R@[R>Q05A3243Rh1B2VRC,>[112y=3=V[[[[[[^06^26^36^86^=6^>6^DRP5%;fRVP0PDPEflC`#MREPwfa,2KRDPf%5PRPP<P8P7P=P4P3PcO=b5b6b7b9b4H0AQ0T,2KS0TQ0>PmQ0BQ0DP^P_PzPvQ0J#DR0?V0iP1%W:Q0K7F;PkPl1lG|,kl,dlR0PxPl%_Y=:l|PxPlPlP|PFPxQ0?ECFTP}P~b:b;b<X06X26X36A66;:P@[10Y9108:RYQ0Q[[[^06^26^36P5PDPfP<P=P\PtO6b5b6b7b9b4Q0>PmQ0BQ0DP^P_PzPvQ0;#SRmQ09'9#DR\Q0E,9m#D/mi7V\P1Q0UPkPlPlPsP]PxPlPl17]b,7F17|HR]PxPl17Gr=:l|A:l]G5hlPxPlP0PxPlPl1~`UPxPlPlP]P`PxPlANlGU9RlBPxQ0RCaECD}FTECECP}P~b:b;b<X06X26X36X86X=6X>6XDR%;711=yRB=3;jQ051>QCPC[\h[\>\A[[^06^26^36^86^=6^>6^DRP5PVPPPEPwPDPfP<P9P8P7P=P4P3PcO>b5b6b7b9b460RcS05EjP6PcP;12K5RcPcP;%?QRD#5RwDnQ00P;O1fgP;O156N[^1LXL6PqPcPcPqQ03DnPuQ0APnP;PtPo12K;Ro,0IRt11IwRu,BoRq'>S03%5QRc/1yRN,1IRE,BoRP,>tRVPtPqPtPP%rtS00PW1B;5#rXK6X16S0RPoPo%<oS0UPuPEPWPWPWP{PIPI%<IREPwPNPWPWPJPDPNPMPQPc%<cCbRNELM:KL04J05P5CUPV%?ZRP#5RR,1nRAQ0A9HK<R<'0R>%5ZRh/1yRC,1nRj/0<RUPWQ0CPAPjPWPWPWP{PnPn%<nRjPRPCPWPWPJPPPCPMPZPh%<hCbRZELM:KP<P<%<<RCGZPQCUPU%oOROQ0<#;R]P^P_PzPvQ0I,9X#DR0Q0H,9p,9m#DR\AV0\i9V\03VP1Q0MQ0LQ0:7F97F;R\PkPlPlQ06#q#Y/7bRb,7`R017F|R[PxPlA:l`GANlG05RlPxPl17Hr=:lFA:l[H5hlPxPl1lHF,kl,dlPxPlA:ls|PxPlPlPFP`PxA:lFGANlG[5RlECFTFTECP}P5P:Q0PQ0OH01b:b;b<X06X26X36X86X=6X>6117yRy115:538P7P:P:P7PBDnA37S:11:8R[/07'iA66=9P@[%;=107310=2Rs11=47O2[[[[[[^06^26^36^86^=6^>6P5Q0=PgQ01Pf12K2R0Q0@,2KRKP8P7P4P3PePTO<b5b6b7b9b4bGQ03PVPtPqPtPWPMPcO1RcO1Rt,1IRq,BoQ00PWQ0RPoPoQ0UPuPqPWPWPWP{PIPIPEPwPtPWPWPJPDPcPNELM:KL04J05P5CUPVP>PUPWQ0CPAPWPMPhO1RhO1RM,1nPWPWPWP{PnPnPjPRPMPWPWPJPPPhPZELM:KP<P<PCGZPQCUPUPOP]P^P_PzPvQ08#SRvQ0G'9,9p,9m#DRmQ0F,9v,9X#D/mi7VmP1P\PkPlPl17HbRb17|`R`PxPlA:lHGANlGb5RlPxPl17Fr=:l|A:l`F5hlPxPl1lF|,kl,dlPxPlQ0NPx%_a,7F=:lG%_d,7F9NlG5Rl,dlFTFTECP}P~b:b;b<X06X26X36X86X=6X>6A39y[118B9OY:A3:S8A38=:'iA6697P@[P7PaP=AQ=7dCIP@[\s[[[[^06^26^36^86^=6^>6P5Q0=PfPgPKP0Q01P8P7P4P3PTO;b5b6b7b9b4bGO7WWX1LQ0TQ05EjK0@bNb_b\bOWdWSP;P5O2n2001000000121000000bgWCXn?P5O1n0110000020011100P2O1WHWVP;P5O2n2001000000121000000bBbbb[WCWTW^W`WZWfWXP;P5O2n2001000000121000000WBWHP;P5O2n2011000000121000000WBWcP;P5O2n2011000000121000000WBWaWYWUWRXm?X?6X@6XALWpXJ6Xi6Xo6WjWkW]WIWPWMWQo"). Qed.

(* [comment removed for export] *)
Lemma bd_keep_postm : forall C A Ak A' m M1 mk m' md' (s bil pixs : Z) v,
  Cok C -> W C A' m' md' -> (c_top C - LSTK <= s - 48)%Z -> (s <= c_top C)%Z -> (0 <= pixs)%Z -> (pixs + 64 < 2 ^ 64)%Z ->
  bd_keep C A Ak m M1 mk s bil pixs v -> POSTM C A' (s - 48) mk m' -> sub_live A' Ak -> live A' (Z_to_bv 64 pixs) = Some 64%Z ->
  bd_keep C A A' m M1 m' s bil pixs v.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilDW ()) ["BilDW"] "p'0h04__x1h11xh21ah34__x2h41kh51qh61Hh77__arithh84__ffh97__sat17h:7__sat18h;7__sat19h<8__varmaph=5__with>4__x3h?2Hah@2HxhA4__x4hB1mhC1ohD1AhE2A'hF2AkhG1ChH2CKhI1FhJ2FMhK2FRhL3H1ahM3H2ahN3HW'hO3HhihP3HlohQ4KEEPhR2LKhS2LVhT2LphU3Lp'hV2LqhW2M1hX2NqhY3NrchZ2PXh[3Rp1h\3Rp2h]3SUBh^4SUB'h_2T1h`2T2ha2T3hb2T4hc2T5hd3bilhe2m'hf3md'hg2mkhh1nhi4pixshj1shk1vhl1yhm1zi005ck_ali016ck_imgi026ck_sp0i038ck_sp0hii046ck_topp%0p&0p;3p;2p;1p;5p;8p;4p;:p;6p;<p;@p;;p;7p;9p;Bg004Hk30ITg00hgk30HTg005Qk30:Tg006Zj2vTg007[j15Tg008@j1hTg008^j1eTg009Aj1YTg00ilR0j5aTg00k0j8uTg01NXj4?Tg00S2j1WTg00P5j1;Tg00o;j24Tg00@MS00j21Tg00BIR1j23Tg00l2k20?Tg00Bfj2ITg00lOl:HTg00mJj5>Tg00:fj2bTg00@ij28Tg00;Hj30Tg00<cj16Tg00nQj2DTg00Fhj1fTg00OVj1JTg00oXj39Tg01O\j6_Tg01>ej4oTg016Aj1nTg01P_j4\Tg014cj2VTg01Qck10GTg01Rhk30FTg00CBR2j2BTg01SEk80ETg01TRl<mTg001Zj6lTg01;hk20DTg01<Pk30CTg01U[j2[Tg00FHk10BTg00GHj2TTg00Gfk10ATg00HDj4PTg00Hbk10>Tg00I@k10=Tg00Ikj2OTg00JNj2MTg01VLj3ZTg00;bk10<Tg00KUk209Tg00D^j2LTg00L7k208Tg00Lck307Tg00MBk406Tg00AiR3j1cTg00C]k105Tg00D;k404Tg00WLl<~Tg01=4j2NTg01FRj3STg01G;j2|Tg01Ggj3}Tg00XUj3dTg01Ajj3{Tg00Q8k401Tg01Vol@zTg001>j6yTg01Wkm;03Tg01Y2l;xTg00Y8j7wTg01CZk30;Tg01Z:j6tTg00Qcj4QTg009cj4gTg01;0j4sTg01EPj8iTg01[Gm90@Tg00T7j4jTg00X1j7kTg00Y\j8rTg00VAl<qTg00VflBpTf0R4#5#5p=Uf2R5f1R6'4/14p=Cg00[>R7/14p=7f6R8f5R9f4R:f3R;1856Cg;04p=@P:P;P5P6Cg=094p=:11:;1364,I5'Bp=<g01HkP5P6P4Csp=2P8P9P:g01J=R<P;P5P6P4Gip=F1B64,B5p=Gf7R=P8P9P<P:P;P5P6P4N90@p=KP=P8P9P<P:P;P5P6Gi/B4p=R%54#5#5#5p=E1356/14p=]P5g00\CR>g00\bR?P?g00]BR@g00=aRAP6g00[\P4Cjg00]bRBFkp==P;P>P?P?P@P5P6P4Grp=Ag00Z@S01PAPAPAP3P3P9P:P;P5P6P4M<qp>02PAPAPAPAPAPAP1P4P6P5P1P;P:P9P8P=f8R1f9R3MBpp>001156/B4p=`PAP6g00^BP4Cjp=XP6P>P?P?P@P4PBFkp=^p,2ALRBp,2CLRCp,3ASRS02:0IBCRD40HB0:BCDRE,vBRFg00=<RG#5RH#5S03#5RI#5RJ#URK#hRL#eRM%hI#eRN#YRO[RPg01Kag01LWPBPCPDP<f<RQDaPBPCPDP<f=RRf:RSP8P9GuPBPCPDf>RTC?g01\KRU%WGRV#5#URW#5#;RX,493CPBPCPDf?RYC?,18%79%;KRZ,38%;HR[00?ZR\'IfBR]fAR^f@R_PTPRPQP3P1P=P8M:HP2PBPCPDP^P]D>%YAR3PBPEP^PLP11bAZR`F@P3PBPEfDRaP51bA6RbE:18LR90M;#61DL:Rc1DL5RdPdPcP;D<Rc%WH#U#;Re,3T1DL;RfPfPT%;WRWD<#6PaP:O1fFRgP:O150O[[[[^1M^4A^5Mf;Rh/4XRi/14%;IRI,36Rj/1Q%fN#YRN18L5Rkg00Z_S04#JS05#JRl#JRm#JRn#J#J#J#JRo52_A2^ko30[[^2APBPCPDfCRpPSPYPRFFA9R1=3G3GPBPCPDPaP^PiPTPRGKPBPCPDP]PpD>P3PBPEPp18LhRiP`E:fGR1PgPaPpP]P_PTPRPQPhM:H[[[P4PBPCPDPpPaD>P3PBPEPaPiP`E:P3PBPEP1P5PbE:18L_90M;#613^ePfPfP^PWD<#6P1P:O1fIRiP:O150O[\c[[^1M^4A^5MACTX411jYA2pkoA2akoR=50N[[^2APBPCPDPgPRP]P_FFA9_hS3G3GP2P3PBPEfERqPLPQP`F@P3PBPEfHRrP5PbE:18L^90M;#613]ePfPfP]PWD<#6PrP:O1fJRsP:O150O[\c[[^1M^4A^5M14YXRt/1411j_A2qko90N=[[^2APBPCPDP1PTPpP^A9^QhGR3GPBPCPDPrPqPtP]P^GKPBPCPDPgP1D>P3PBPEP1PLPYP`F@fKRtPsPrP1PgPaP]P^P_PYM:H[[[P4P3PBPEP1PLPTP`F@P3PBPEPtP5PbE:18La90M;#613qePfPfPqPWD<#6PtP:O1fMR=P:O150O[\c[[^1M^4A^5MAC]X411jpA21koA2rkoRu50N[[^2APBPCPDPsP^PgPaA9aYTGR3GP2P3PBPEfLR^P5PbE:18Lq90M;#613gePfPfPgPWD<#6P^P:O1fNRvP:O1Rw50O[\c[[^1M^4A^5M14pXRx/1411jaA2iko90Nu[[^2APBPCPDPtP]P1PqFFA9q_Y3GPBPCPDP^PiPxPgPqGKPBPCPDPsPtD>P3PBPEPtPLPpP`F@fORxPvP^PtPsPrPgPqPaPpM:H[[[P4P3PBPEPvP5PbE:18L1Ru90M;#613rePfPfPrPWD<#6fPRyP:O190Ow[\c[[^1M^4A^5MACgX411j1A2tkoA2^koRw50N[[^2APBPCPDPvPqPsPrFFA9rp]3GP2141XRz/1411jrA2=ko90Nw[[^2APBPCPDPxPgPtPiA9iapGRPBPCPDPyP=PzPsPiGKPBPCPDPvPxD>P3PBPEPxPuP`E:fSRufRRzPyPxPvP^PsPiPrP1M:H[[[P4ACiX411jsA2vkoA2xko50N[[^2APBPCPDPzPiPvP^A9^1gGRP2PBPCPDPuPsPxP=FFA9=r1PBPCPDfTRrfQR114tXPvP=GKPBPCPDPzPuD>P3PBPEPuPLPtP`F@fWRgfVRiPrPuPzPyPvP=P^PtM:H[[[P4PBPCPDfUR=P^P1PxFFA9ytsPBPCPDPgPr14vXP1PyGKP2PBPCPDfXR214xXPzP1FFPBPCPDP=PzP1E_PBPCPDPiPgD>P3PBPEPgPLPxP`F@f[RvfZRsP2PgPiPrPzP1PyPxM:H[[P4PBPCPDPs141XPrPuFFPBPCPDP2P=PrE_PBPCPDfYR2PsD>P3PBPEPsPLPzP`F@P1PBPCPDP<f^R1DaP0PBPCPDP<f_R0f`RzP0f]f\PvP2PgPiP=PrM:HP4PBPCPDfdR=Co#n%5K#U#ERK#;'3PBPCPDP=C?7]UPBPCPDfeRiC?PBPCPDPiC\,DL'1PBPCPDffRgC\,DL%5KRK#5#E#E#E#E#E#E#E#E#;R2'1PBPCPDfgRvC?%;JRJ'V=0A7&0G<:0FAAPBPCPDfhRsCo#n'1g01]N%;K90AUPBPCPDPvfiRKD>P3PBPEPvPLP0P`F@R`P3PBPEfjREP5PbE:Rb18L=90M;#6R313iePfPfPiPWD<#6RWPEP:O1RffmReP:O150O[\c[[^1M^4A^5MRxfbS06?CX4RyfcR^,1jRjA2gkoA2skoS0750N[[^2ARwPBPCPDPEfaR{PgP^FFS08A9^01S09'BR|'BR}'BR~'BPBPCPDPvPsPKPRPrL0EP`P~PQPxP}POfkR}P:O1fnRxP9O190O4XCOPuP8P9P:PaP8P9P;O3P5P6P4O7PfPBPCPDPxP}PEP8P9P:PqP;P6M<mElXYWX@cXX3XVbX1MX4AX5MPwP|PNA2vko18L;=2vo=0N4XCNPBPCQ02p,4PINSp,3P16Pe14=XPvPgP5PoPzP]20D[ZR]1I7[%7Z1I7\[[Rv%7[Reg00>\RNB0C[Z6UW?Rk%7\\N^?eRePBPCPDfoC?RN/[JR|%7N%7JRNPBPCPDfqS02C?Rw/VJ#7[[Rbg00`1R3$0BRc%f3RWPA1TA5S0:P6&0AARqCPS0;&0>AR}&0=ARf1OAGRG1MAXRu5ZARO1OAHRH5=fRQ&0<?R~PQCA209f@RQP4P5g00`]R`g00a=Rr'L20845=0`rdB07A76H06Rrb8b<b=X0AX3A144XR`/16AC6X5[^0A^3AP4P8PsP9O3b7b9b:b;%coS0<,35S0=/1\S0>135IS0?/1\PAPAQ00P4X1ARRQ001164$05XlAX1AQ0=Q0?PRPRPRPAPAg00_M1364H04,LAXBAXhAP5P51LA5Q0<PIPRPRQ01%c4,LAW1PoPI1LAIJ02N:00P\P\1LA\M<~P]PvPkPeP|Pb1NAn1NAm1NAlQ05,NAQ04,NA5SA5SA5SA5SAg01K5'|=}3cPWPAPA1TA;R3P5PqCPP6PAPqP:1TA:CPCPP}Pf1MAI9dAGRqQ03,OARl5=fP~Pf%WV,OARm1MA25=fP~PfA=fHmP~PfA=flHP~1MA[={ALR[9=fqCACACACAPQPrb8b<b=X0AX3AX>AXAAA]4I511:211;9119:A]:I\[[[[^0A^3A^>A^AAP4PBPCPDQ02C\,DLPsPwP8P:PSPhP{O8b7b9b:b;H01Q0>eP]PvPkPeP|PbPcPWPAQ0:P6P3CPP}PfAZAGH1OAV=ZAu5=fRuP~PuCAPQPrb8b<b=X0AX3AX>A145X9C4614;X9C65[^0A^3A^>AP4PsPUPwQ06O4b7b9b:b;M@zQ07PtP5P6P4O3EyXMjXLyX2AQ08Q09PBPCPDP<PEP{PgP=P^PaPBPCPDP<PE14{XP{P=P^PYP]PvPkPePBPCPDflC?RY/[J%7YPBPCPDPxC?Rx/VJ#7\N[PcPW1TA6RYP}A=fOGPQPrb8b<b=X0A11`4^0AP4PiO1b7b9b:b;N;03M;xP=P^P0P1PpPz1DL4RpPpPzPZD<PBPCPDPKPgPi18L{RgPZP6P_PTPAP{134ZRT,Id9`4dXmAP]PvPkPe1[xJRd%7xPBPCPDfpC?/VJ#7\N[RNPcPWQ0;P}PfPfP>P?P?P@A=fGH1MAZ9dAGR@,XH,^fFwRHP~PHCAPQPrb8b<b=X0AX3A1I6T9`46P6P5P5P6PZD<[^0A^3AP41DL9PiP:O3b7b9b:b;1DLgP]PvPkPePdPNPcPWPYP}Pf1MA7==fGR7P~P7CAPQPrb8b<b=X0A%74%76[^0AP4PiP0O2b7b9b:b;P]PvPkPePdPNPcPWPYP}Pf1X@[,^fP~1XG[,^fCAPQPrb8b<b=X0A1IT\1I6\[^0AP4PiP1O2b7b9b:b;60;{ElM<mW@X1MEtCQCQCQCQCQbSWcWbWaW`W_P:P;P5P6P4O5n5000001000000151104102103100101b6WUW^WRWIP6P4O2n2001000000121000000W6WZWJP6P4O2n2001000000121000000W6WKP6P4O2n2001000000121000000W6WQP6P4O2n2001000000121000000W6WTP6P4O2n2011000000121000000W6W]P6P4O2n2011000000121000000W6W\W[WOWPWNWHWkXiAXdAXjAWfXePXgPXWPWBXEFXFFWDWGo"). Qed.

Lemma bd_thru_postm : forall C A' mk m m' (s bil : Z), bd_thru mk m bil -> POSTM C A' (s - 48) mk m' ->
  live A' (Z_to_bv 64 bil) = Some 104%Z -> (4096 <= bil)%Z -> (bil + 104 < 2 ^ 64)%Z -> bd_thru m' m bil.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilDW ()) ["BilDW"] "h04__x1h17__arithh24__ffh37__sat17h47__sat18h58__varmaph65__with74cstrh84__x2h91zh:2Hah;4__p1h<4__x3h=2A'h>1Ch?2G1h@2G2hA1HhB3H1ahC3H2ahD2LKhE2LbhF2THhG2_HhH1ahI3bilhJ1mhK2m'hL2mkhM2nnhN1ohO1sp;3p;2p;1p;9p;8p;6p;4p;7p;@g004Hj3mTg00hgj3lTg005Qj3YTg006Zj2UTg007[j12Tg008@j1NTg008^j1KTg009Aj1BTg01^Uj3DTg00S2j1>Tg00P5j14Tg00o;j2ETg01[Gl9kTg01EPj8OTg01O\j6MTg00@ij2=Tg009cj4LTg00:fj2]Tg00;Hj3;Tg00@Mj20Tg00BIj21Tg00l2j2XTg00Bfj28Tg00Aij1<Tg00CBR0j2JTg00AOj2ITg00Fhj1HTg01;0j4ATg00PSj1WTg01;hj2VTg01<Pj3TTg00FHj1STg00GHj2?Tg00Gfj1RTg00HDj4GTg00Hbj1QTg00I@j1PTg00Ikj2@Tg00JNj27Tg00XUj3:Tg00;bj1jTg00KUj2iTg00D^j2gTg00L7j2fTg00Lcj3eTg00MBj4aTg00nQj2`Tg01Ajj3_Tg00T7j4FTg01CZj3^Tg001Zj6CTg00K1j6bTg00Y8j7cTg01HGj7dTg01_Pl@\Tg001>j6[Tg00X1j7hTg00Y\j8ZTf0R1#2#2p=5g00=aR2f1R3g00[\P1CFp=6P3g00\CR4g00\bR5P5g00]BR6P1g00]bFhp=3f3R7P4P5P5P6f2R8P3P1GZp=9p,2ALR9p,2CLR:p,3ASR9m9:R;3lAY9:;R<,U9g00=<R=#2R>#5R?#2R@#5RA#NRB#K%N?#KR?#B[RCf4RD?D71P9P:P;g01J=REf7RFf6RG%>=RH#2RI#2#5RJ#4RK,E8f5RLP7M9kP0P9P:P;PEf8R01E7KPGPDGOP9P:P;PFPGPDEM%B2RMP9P<P01=B7RNCL%>I#2#5#4RI,]2RO3;%5A#5#5#4RP/0D11LI%4>RQ%4ARA'XRR'8f9RS=D0G[[[P1P9P:P;PEf:RE1ELKP0PGGOP9P:P;PEPSPFEMP9P<f;R<1=BGCL=;MO10PF110I/8Rg00Z@%4@R@,1</03%<3,18ROf<RM%>>#>#2#5#4RE'1'0%2J#4RJ,1M/0811MI,0O'J'I%H?#BR?g01HkROfARKPNP8CAPOf@RT1=BDP7CA=;?1XN?P9P:P;POfBPKf?f=R;,=BR:PIP7P8PFPGP2P;101DX92%W8R9g00[>R?%<8'0RU1VQARV18?Q10?A18?R[[RW10?QRXg00>\RYATQA3UW:RA10?R\Y^:XRXg00`1RY#SRZ%HYRYP21?28R[P3%R2CG%Q2R\%P2R]1@2=R=172@5:21@2>R>'6,3]%j5R^16=>,3]C91i]6R_P1P8g00`]R`g00a=Ra'g1f18=;`adAe2?3CaRab2b5b6X02X82111@/031038[^02^82P1PFPKPLO3b1b3b4b71`B:R:P9PUPVPWPAPXPZPY1?23R@P\P]172P/6=,3]P^172?/6=,3]C9P_Pab2b5b6X0210P110?3[^02P1PKPSO2b1b3b4b7P9PUPVPWPAPXPZPYP@P\P]P2172IR?9:2=RPg00^BR`172Q=_2BRBCF,3]RQP^P2P=P`PBCF,3]C9P_Pab2b5b6X02111IR`/8RRb183R[^02P1PKP0O2R0b1b3b4b75^;RcECP2P;%<7,1D/0`X92P9PUPVPWPAPXp-0RdPZPYP2P[P31?27CGP\P]P]P4P5P5P6A:2=>R>1@2HRH172E5:2'6,3]P]P4P5P5P6P]P4P5P5P6PLEbA:2H?,6>,3]R>FcFdP^P>C9P_Pab2b5b6X02X82X<2W;1113R>118E'0118I,0>,J7'I1138117I'0[^02^82^<2^;dP111KJ/0FPK%<GPFPDO5b1b3b4b7P:PcECP2P;10`RX92P9PUPVPWPAPXPZPYP@P\P]PQP^16PB,3]C9P_Pab2b5b6X02113I/0R\b^02P0b1b3b4b7P:PcECM@\POPTPNP8CAPMP7P8P3P1O4E[WCWBWMXH2AD<MSeW@W?WEWDWGP3P1O2n2001000000121000000WAWFXI2XO2XKCXJCWLW=W>o"). Qed.

(* [comment removed for export] *)
Lemma bd_keep_postd : forall C A Ak A' m M1 mk m' md' (s pp bil pixs : Z) v,
  Cok C -> W C A' m' md' -> (c_top C - LSTK <= s - 48)%Z -> (s <= c_top C)%Z -> (0 <= pixs)%Z -> (pixs + 64 < 2 ^ 64)%Z -> (0 <= bil)%Z -> (bil + 104 < 2 ^ 64)%Z ->
  (bil <= pp)%Z -> (pp + 8 <= bil + 104)%Z -> live A' (Z_to_bv 64 bil) = Some 104%Z -> Z_to_bv 64 pixs <> Z_to_bv 64 bil ->
  bd_keep C A Ak m M1 mk s bil pixs v -> POSTD C A' (s - 48) pp mk m' -> sub_live A' Ak -> live A' (Z_to_bv 64 pixs) = Some 64%Z ->
  bd_keep C A A' m M1 m' s bil pixs v.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilDW ()) ["BilDW"] "p'0h04__x1h17__arithh27__sat17h37__sat18h47__sat19h54__x2h64__ffh78__varmaph85__with91xh:4__x3h;1ah<1kh=1qh>1Hh?4__x4h@2X0hA4__p1hB4__x5hC2HxhD1XhE2_HhF1ihG1zhH2HahI2INhJ2LqhK2NqhL4TOPbhM4__x6hN4__x7hO2a0hP3bilhQ1mhR1ohS1yhT1AhU2A'hV2APhW2AkhX1ChY2CKhZ1Fh[2FMh\2FRh]1Gh^2G1h_2G2h`2G3ha2G4hb2G5hc3H1ahd3H2ahe3HW'hf3Hhihg3Hk0hh3Hlohi4KEEPhj2LKhk2LVhl3Lb'hm2Lphn3Lp'ho3Lq'hp2M1hq4NEpbhr3Nq'hs3Nrcht3OFFhu2PDhv2PXhw2Q1hx2Q2hy3Rb1hz3Rb2h{3Rp1h|3Rp2h}2Rqh~3SUBi004SUB'i012T1i022T2i032T3i042T4i052T5i061bi071li082m'i093md'i0:2mki0;1ni0<4pixsi0=2ppi0>1si0?1vi0@5ck_ali0A6ck_imgi0B6ck_sp0i0C8ck_sp0hii0D6ck_topp%0p%1p&0p&1p;3p;2p;1p;5p;8p;4p;:p;9p;7p;6p;Ep;Ap;?p;@p;;p;<p;Bg004Hk31=Tg00hgk31<Tg005Qk30jTg006Zk20_Tg007[j1;Tg008@k10MTg008^k10JTg009Ak102Tg00ilR0k50HTg00k0k80^Tg01NXj4:Tg00S2j1kTg00P5j1ETg00o;j24Tg00@MR1j20Tg00BIR2j22Tg00l2k20nTg00Bfj2<Tg00@ij21Tg00:fj2pTg00lOl:XTg00mJj5NTg00nQj25Tg00<cj18Tg00;Hj36Tg00Fhk101Tg00OVj1UTg00oXj3JTg01P_k40:Tg014cj2GTg01Qck10vTg01Rhk30uTg01>ek40QTg01`Ym90TTg01a]k70UTg01bbk20NTg010_k10mTg011]k108Tg012Tm90lTg013Xm90kTg015Cj1rTg016Aj1qTg0179k207Tg017nk406Tg00;bk10LTg0192k205Tg01:1k203Tg01@ck10KTg001Zj6oTg00@1k40hTg01;hk20gTg01<Pk30fTg01U[j2bTg00FHk10eTg00Hbk10dTg00I@k10cTg00Ikk20ITg01Ajk30bTg00JNk20GTg00KUk20aTg00D^k20FTg00L7k20`Tg00Lck30]Tg00MBk40\Tg00CBS00j2BTg00Gfk10[Tg01BMmE0ZTg01=4k20ETg00T7j4eTg01SEk80XTg01chmA0BTg01e6m?0WTg00AiR3k10ATg01fEk10VTg01;0j4STg01gCk31;Tg001>k60@Tg00AOj2OTg00C]j1CTg00D;k41:Tg01h>j6}Tg01hfj6FTg00Eak40>Tg01=]m?15Tg01CZk30=Tg01iPk614Tg00Q8k40STg01jUj5sTg01k\j2zTg01l]k212Tg01mak211Tg01nek60PTg01okm@0~Tg0212k20;Tg0224k50<Tg01Y2m;0|Tg01Z:k60zTg00Qcj4uTg009ck40yTg01EPk80OTg0236m:0wTg00GHk20xTg00XUk30tTg00X1j7wTg00Y8k70}Tg00Y\j8tTg01FRk309Tg01G;k20sTg01Ggk310Tg00HDk404Tg01HGk713Tg00Tbk60qTg00K1k60pTg00VAm<16Tg00VfmB0oTg00WLm<17Tg01VLk318Tf0R4#;#;p={f1R5g01\KS01'4/04p=Qg00[>R6/04p=3f5R7f4R8f3R9f2R:P5H0y;64p=9A6:54#8p=A10891254,<:'Bp=m1254,<:p=d129:/05/B4p=Tf6R;g01HkS02P7P8P9CSQ02P:P5P4CS36p=>P;P7P8g01J=R<P9P:P5P4L0Op=[1B54,B:p==P4P5P:P<P9P8P7P;f7R=f8R>N:0wp=]14:5/04p=RQ02P:P5P4CSp=vQ02P9P:P5CS=684p=nQ02P:P5P4CS9689p>0?P=P;P7P<P8P9P:P5L0O/B4p=yP9P:P5P4H0Q#qp=`%;4#;#;#;p=P12:5/04p=7g00=aR??646p=|%q4,05p>0r1<54,B:p=Y%85/B4p=H1154969:p>0i20x?4p=a20G?4p=VB0t?54p=LP:g00\CR@g00\bRAPAg00]BRBP?P5g00^BRCP4Ceg00]bRDFwp=MP:P@PAPAPBP?P5g00[\REP4CePDFwp=?P:P@PAPAPBP5P4K0}p=WP;P@PAPAPBP7P8P9P@PAPAPBP:P5P4GtGtp=xP9P@PAPAPBP:P5P4Gtp=_1054,O:p=D20E?4p=^B09?54p=gB09?54:09?:p=lg01K5-0s4p=jg00`1RF@1054p=cP?P:P5P4H04p=\P?P?P8P9P:H04P5P4H04p=f20I?4p=IP:P@PAPAPBP5P4K13p>0DP5P@PAPAPBP4PDFwp>0YP5P@PAPAPBP4J0qp>00P5P@PAPAPBP4J0pp>0CP7P@PAPAPBP8P@PAPAPBP?P9PEP:CePDFwP5P4Gtp=@20F?4p=Kg00Z@S03P?P?P?P3P3P7P8P9P:P5P4N<16p>19P?P?P?P?P?P?P2P4P5P:P2P9P8P7P;P=P>f9R2NB0op=~P?P?P1P=P1P;P7P8P9P:P5P4N<17p=Z10:5/B4p=hB18?54p=iP8P@PAPAPBP9P@PAPAPBP:PDFwP5P4Gtp>0RP?P5PCP4Cep>0{p,2ALRCp,2CLRDp,3ASR:1=CDR@41<B0jCD@R1-0_CS04Q04Q04g00=<R3#;S05#;S06#;S07#;RE#{RG$0MRH$0JRIQ07$0M$0JRJ$02RK[S08Q08Q08Q08g01Kag01LWPCPDP@P<f=RLI0HPCPDP@P<f>RMf;RNP=P;L0^PCPDP@f?S09C:%k3S0:#;S0;#;S0<#;RO#;#ERP,4;S0='QPCPDP@f@S0>C:,0=%37%EGRQ,2;Q05#ERR00nQRS'<%3>Q0;#kS0?#;#{#ERT,22S0@/<Sf:RU/0Nf<RVQ07#ERW'2S0A12NT'0&02?RXPCP1fDRY11HVS0B1p?TE9Q0B11HLS0C5AIfIRZfHR[fGR\fER]PYfCS0DQ0>PMPLPVM:XQ00PCPDP@P[PZDNPXPCP1P[11HMS0E1p?QR^E9PXPCP1fKR_P:1p?5S0FE9Q0D,1H9AI915H8R`15H:S0GQ0GP`P9DmR`PYQ05#kS0H#{#ES0I15H9Ra%EORO9daYCT#8P_P8O1fMRbP8O156K[[[[^9I^<?^=IfBS0J/4PRc/04125WRdQ0D'0&01J$02ReP\11H:Rfg00Z_S0K#US0L#US0M#US0N#US0O#US0P#US0Q#US0R#URgP[PfPgF>[[^;?PCPDP@fJRhfARifFRjPYF[AJYML3=3=PCPDP@P_P[PcPiP]PYM9]PCPDP@PZPhDNPXPCP1Ph11HiRcP^E9fNRkPbP_PhPZP\P]Q0DQ0JPiM:X[[[P4PCPDP@PhP_DNPXPCP1P_PcP^E9PXPCP1PkP:Q0FE911Hj9AI9P\Q0IPaAda\OCT#8PkP8O1fPRcP8O156K[\`[[^9I^<?^=IAR]P410djPePhPfPgAv_fgRlDn[[^;?PCPDP@PbPYPZP\F[Q0>9J\i3=3=Q00PXPCP1fLRmQ0J,1HP^E9PXPCP1fORnP:Q0FE911H\9AI9P[Q0IPaAda[OCT#8PnP8O1fQRoP8O156K[\`[[^9I^<?^=I14jPRp/0410d\PePlPmPfPgI0?[[^;?PCPDP@PkP]PhP[Q0J=J[iGy3=PCPDP@PnPmPpP]PZP[M9]PCPDP@PbPkDNPXPCP1Pk11H]P^E9fRRpPoPnPkPbP_PZP\PjP]M:X[[[P4PXPCP1Pk11HYP^E9PXPCP1PpP:Q0FE911Hh9AI9P_Q0IPaAda_OCT#8PpP8O1fTRlP8O156K[\`[[^9I^<?^=IARZP410dhPePkPfPgAvnfgRqDn[[^;?PCPDP@PoP[PbP_AJ_]YGy3=Q00PXPCP1fSRrP:Q0FE911H_9AI9PmQ0IPaAdamOCT#8PrP8O1fURsP8O1Rt56K[\`[[^9I^<?^=I14hPRu/0410d_PePqPcPfPgI0?[[^;?PCPDP@PpPZPkPmF[AJmj]3=PCPDP@PrPcPuPZPbPmM9]PCPDP@PoPpDNPXPCP1Pp11HZP^E9fVS0SPsPrPpPoPnPbP_PhPZM:X[[[P4PXPCP1PsP:Q0FE911HbRu9AI9PkQ0IPaAdakOCT#8fWRqP8O196Kt[\`[[^9I^<?^=IARbP410dkPePpPfPgAvrfgRtDn[[^;?PCPDP@PsPmPoPnF[AJnZ[3=Q0014kPR[/0410dnPePtPlPfPgI0?[[^;?PCPDP@Q0SPbPpPcAJchZGyPCPDP@PqPlP[PbPoPcM9]PCPDP@PsQ0SDNPXPCP1Q0SPuP^E9fZRufYR[PqQ0SPsPrPoPnPkPbM:X[[[P4ARcP410doPePsPfPgQ0SPfPgF>[[^;?PCPDP@P[PcPsPrAJrbmGyQ00PCPDP@PuPoQ0SPlF[AJlkbPCPDP@f[RkfXRm14pPPoPsPlM9]PCPDP@P[PuDNPXPCP1Pu11HoP^E9f^Rnf]RZPkPuP[PqPsPrPpPoM:X[[[P4PCPDP@f\S0TPrPmQ0SF[AJqocPCPDP@PnPk14sPPlPmPqM9]PCPDP@Q0TPZDNPXPCP1PZ11HlP^E9PrPCPDP@P<faI0HP0PCPDP@P<fbS0UfcR0Q0Uf`S0Vf_PnQ0TPuPmPqQ0SM:XP4PCPDP@fgRqC`%{G#PS0W#;RG#ES0X'2Q01PCPDP@PqC:37PCPDP@fhS0YC:PCPDP@Q0YH0:,5H'0PCPDP@fiS0ZH0:,5H%;GRG#;#P#P#P#P#P#P#P#P#ES0['0PCPDP@fjS0\C:%EERE'G#|&0v<S0]:0u??PCPDP@fkRmH0Q+0rg01]NQ01%EGS0^56?PMPCPDP@fmRGQ0\fdRu/4PP0PqffS0_M9]Q00PCPDP@P<fnRnfe/4PPuQ0YPqN90TPCPDP@PmPuQ0YPqK0UfoRrPnflRlPmQ0\Q0YQ0_PuP0Q0UM:XP4PCPDP@P<fpR014qPQ0_Q0\Q0ZN90TPCPDP@PnPqPmQ0\K0UPXPCP1frRuP:Q0FE9S0`11Hm9AI9S0a20Nn9S0b&0m;15H;S0c#3Q0c;YSPCP1fwRZfsRk&08uRoP=P;PCPDP@P<fzRcPZPkPuPmN90lP8N90k%3;15H=S0d/GE#|Q0d%r;%qo%34Ro%r=Rp7Y4PCP1fyS0e20725R[H06fuRtP[O1&0LJRJ5AK205C[203C[#8'H3=[^F?CT3=Q00%3=15H>R[/GE#|&08k#q97[p%r>9Yo4PCP1Pc207U5R[H06fvRpP[O1=AKJ205C[203C[#8'H3=[^F?3=g00>?S0fP4%3215HNR[/GE#|%rU&08p#q57[%rN9Yo4PCP1f}S0g207L5R[H06Q0eP[O1=AKJ205C[203C[#8'H3=[^F?3=PIPVPXPCP1Q0gP41p?VE9Z06IP215HV,1HR[&0KVEoPXPCP1f|S0hP[1p?NE915HL96?tR[PUP?15HMS0iPIQ09PHP4H0iXP?PIQ0i,1HPM&0KMH0hPpP4EoO1WD%8[R[eP[PCPDP@P<p+01BS0jf~S0kPcQ0ePpQ0iPTPLPkPuQ0ZP5P420gRQR[1<6R%3Q1<6S[[Rv%3RRwg00>\RxB0fRQ5UWHRy%3S\x^HwRwPCPDP@p+01DC:Rx/bES0l%3x%3ERxPCPDP@p+01FC:/GE#3[[S0m&0eFRz&01FRF%a5S0n&0d?R{&0c?R|20I?3R3%VTS0o'LS0p%VR>0b?HS0q5M|S0r&0LARAP|20G?6S0s=?|3S0tPAQ0tQ0q9M|3S0u5W|RRFx20a|BRBP4P:g00`]R}g00a=R~+0F20`4:=6}~dB0]?65H0\R~b6b7b8X0?124TS0v/<SS0w%35S0x%3:?Y:S[[^0?P4PcP0fqR}O3b1b2b3b4P[PvPyPwQ0lQ0mPzPFQ0nP{P|PRPAPRC_PBP~b6b7b8X0?AYo4SQ0x1<5SS0y'B[^0?P4Q0J,5HPNO2b1b2b3b4P[PvPyPwQ0lQ0mPzPF&0[?RRP{Q0sQ0o5?|PBP~b6b7b8%3TP4b1b2b3b4P[PvPyPwQ0lQ0mPzPFQ0nP{P|Q0tPAQ0tC_PBP~b6b7b8X0?S0tQ0x\o^0?S0xP4PiP=O2b1b2b3b4NE0ZQ0i97pTQ0i/2L;DpP[PvPyPwPCPDP@p+01ES0iC:S0m/bEQ0m#3PCPDP@p+01GC:/GE#3\x[p-0RoQ0R#^S0RQ0P#^S0PQ0M#^S0MQ0K-0E?S0K'gS0l3l#jS0zQ0zQ0RQ0O#^S0OQ0N#^S0NQ0L#^S0L'g3l#j/cz'c'cPF%a8S0z9\R7P7%a:S0{P7PRP5%a7S0|P7%a9S0}?\7RDfDfP{P|Q0H#IS0~Q0o'LS10Q0H#k#IS0H5?|Q0HQ0?#I'LS0?Q0~5?|60D|PAP|P?Q0~g00a]S11Q0HCe-0Y|-00|PAP|Q0;#IS0;Q0<#IS0<5?|Q0<Q0;%VWS12'LS135M|5W|PAP|Q0HQ0<5?|Q0<Q0?5M|5W|PAP|P|Q13Q10PAP|P|Q0~Q0;PA20C|=E@E@FxFxPBP~b6b7b8X0?X5?X:?X??XB?WAQ0v/0:12:8;D4A6?59Q0f[1097S0;129WS107Y7107;S13127=7Y;127WS0<128T'0Q13PN[[[[[[^0?^5?^:?^??^B?^AoP4Q0fQ0J15HiQ0D,5HQ0hf{RiP8P7PLPMPrP0O<b1b2b3b4bVbrboWEWgP5P4O2n2001000000121000000b>b}WIQ0b#8S0beXC`WKWJX9IX<?X=IQ0`Q0aQ0b\`[[^9I^<?^=IPCPDP@P0PuDNPXPCP1P011HqP^E9S0`PXPCP1PkP:Q0FE9R111Hl9AI9RXPGQ0IPaAdaGOCT#8ROPkP8O1S0IPpP8O156K[\`[[^9I^<?^=IRaARmP4S0F10dlS0aPePrPfPgAv}fgS0bDn[[^;?S13PCPDP@PkQ0\PrPlF[S0?Q0_9JlqS0H'BS14'BRd'BR^'BPCPDP@P0P}PuQ0DQ0SL0XQ0`P^Q0JPaPdPKftRdP8O1PZP7O196K4XRKPsP;P7P8PhP;P7P9O3P:P5P4O7Q0IPCPDP@P<PcPZ14}PRsP0PdPkP;P7P8P_P9P5P=P;P7P8P9P:P5O6NA0BEoXsOXC`XKXXJ1X9IX<?X=IQ13Q14Q0FQ0aPeAv0fgPeP011H9PgP4DnXRePCPDP@P<p,4PINSS14PpPk14GPRfPlP0PrP:PgQ0YP\N?0W10f:&0AgRf=79SPCPDP@fxR1C:14rPRX'QR`A7rW7127fRO;DrS13&0VCRaPk11H;S0IPgCSPaPdQ0IPgCS56e[[[[g024;$01R^Pa10X8RX10OSS0JPCPDP@PcC:/QsRsA7}W=S0`12=f;D}ROP8Pt11H>RaPgCSP8PpPaPgCS56e[[[[Z07^P4Q02p,3P16:1;CDJ0@ARnP9128fS02/0SS0SPCPDP@Q0eC:S0D140PS15'QA70W;12;f;D0PePd11H=R^PgPtP^PgF>[[[R^[PCPDP@P<Q14P1PtP}P011HGS16PTQ0\Q0ZQ0VQ0JPePtPaPgPpPaPgF>Ra\O\s[\XQ0</0SQ0`12=WS0<;D}Pa[\s[\XS0`PXP^PXP5\5XSoX9oR^P4X9?RsPWO1Ra,28S0J/0SS0VP^P`P^A7nW8ROQ0J/0nS17'OS18PeP}11H8S19PgPuQ19PgF>S19O2S1:O2S1;O2%CXQ0SQ13PePkQ0IPgPdQ0IPgF>S0I[\`Q0VQ1;Ps1054#CXS?X9?RXQ02Q0JPsPsPsP?P?g00_M1254H1:#KXQ?Z0;?S1;P8P8%K8PfPaPsPsQ03&0A4#KW9PgPW%KWJ19S03M:~S0VPSPS%KSS13A6?SSeS0SGZP`Q02/0nS1<,OOS1=PePu11H7S1>PgPkQ1>PgF>[P`Q1:%C`Q1=Q19Q18Q19POQ1<POQ17%COPsPXQ02Q0JQ0VPnPn%KnGZE}Q19#CEFEFEFEFP4H0>Q0`P[PvPyPwPCPDP@PiC:RO/bES0`%3OPCPDP@Q0gC:S19/GE#3\x[S0VPzPFPRP{Q0sQ0o5M|PBP~b6b7b81<6TP4b1b2b3b4b@N?15Q0W#ER6Q16,5HROPCPDP@P1C`97OT3hQ0011Hn,5HRO,06PCPDP@Q0eC`97OTQ0IP411H0,5H,0611H},5HPCPDP@Q0hC`77TP?11Hu,5HQ0vPCPDP@Q0kC`S0I'0XG?P4Pu14dPR}/02R612UfS16/0SPCPDP@p+01@C:14pPS0W'QROA7pWVR`12VfS0J;DpPePcQ0CPgPiQ0CPgF>RV[[S0C[[A7UWSQ0A=D`pPV[\O[\6S02P6122fS17/0SS1<PCPDP@Q0kC:S1814tP'QA7tWNRV12NfS1=/0tS1:'OS1>PeQ0eQ0BPgPcQ0BPgF>[S0B[[P6P^122aS1?/0SS1@P^Q19/Q}R}P^A7kW2R`Q1?/0kS1A'OS1BPePp11H2RpPgPZPpPgF>RpO2S1CO2S1DO2%C6Q1<A7dWUQ16;DdPeP111HNR6PgQ0eP6PgF>R6[\}Q1@Q1DPsPXQ17Q1?PsPsPsQ1;P2P2%K2PfPaQ03M:~S1DPSPSQ0SGZP}Q17/0kS1@,O`S16PePZ11HUS1<PgP1Q1<PgF>[P}Q1C%C}Q16PpQ1BPpP`Q1@P`Q1A%C`PsPXQ17Q1?Q1DPkPk%KkGZE}%CpEFEFEFEFP7H0>S1DQ02P[PvPyPwPCPDP@p+01AC:Rp/bES1?%3pPCPDP@p+01CC:R`/GE#3\x[R}Q0tQ0xP4PZPnO2b1b2b3b4b@Q1DQ02P[PvPyPwQ1?P}PzPFQ0nP{P|Q0rPAQ0uC_PBP~b6b7b8X0?S0rQ0wQ0y[^0?S0wP4PZPGO2b1b2b3b4b@60=uJ0@PCPDP@Q0gC`97uTPCPDP@P<Q0kP0J14Q0IQ0X'2Q01Q1837P=Q0W/0NR}Q0J/0SPCPDP@Q0jC:141P'QS0jA71WMS0J12Mf;D1PeQ0hQ09,1HS0WPgQ0gQ0WPgF>S0W[[[[Q0A/0SQ0jQ0J12MW;D1Q0W[[[\}S0jP}Q1=/0SS0W14ZP,QpA7ZWL12Lf;DZPePiQ0EPgQ0hQ0EPgF>[[[P}P^12NaRg/0SReP^POP^10gtS0E,OVR^P6O2RLO2RpO2%C}Q0WQ0CPePpPsPXQ1=PgPsPsPsQ1;PNPN%KNRpPfPaQ03M:~RaPSPSQ0SGZPOQ0BPOPL%COQ1>P6P^P6PVQ1:PVQ0E%CVS0EPsPXQ1=PgPaPtPt%KtS0BGZE}%C6EFEFEFEFP=H0>R6Q0jP[PvPyPw1b`ERa%3`Q0m/GE#3\x[R`PzPFQ0{?\5RS0SP{P|%VPRg,i3Q05#IR^5?|ROPAPOC_PBP~b6b7b8X0?X5?AR4P5AR5P:[^0?^5?P4Q0>PiQ09O3b1b2b3b4b@Q0W12NWRO/0SPsPXQ1=POPsPsPsQ1;PNPNPpPfPWQ03M:~S03PSPSQ13GZP6Q0jP[PvPyPwPaP`Q0OQ0NQ0MQ0LQ0K'gRf'g3l#j/czPFQ0}P:PRP5Q0zP8PRP8PRDfDfP{P|P|Q12,L3RpQ06#IRNPAP|P|Q06#k#IRLQ0[#VPAP|P|P^PLPAP|P|PNP^PAQ0q9?|pE@E@E@E@PBP~b6b7b8X0?X5?X:?X??A74W:Q0[,08Q0;1078128WRL/0S[[[[^0?^5?^:?^??P4PCPDP@Q0iH0:,5HPiQ0mQ0>PMPhP_PkO8b1b2b3b4b@H0SQ0WeP6Q0jP[PvPyPwPaP`PzPFQ0{Q0}7\5P{P|1i3^R_Q0:#IRh/ig5?|RePAPeC_PBP~b6b7b8X0?X5?X:?1445Re14:P'0145:R}149P'0[^0?^5?^:?P4PiQ01Q0mPdO4b1b2b3b4b@Q1>10OtS0W,OVPVQ1:PVQ0WQ0EPsPXQ1=POQ03PtPtQ0BGZE}P6Q0jP[PvPyPwPaP`Q0RQ0Q#^Q0PQ0N;lf3l#j/czPF%a=?\8RP:PRP5Q0|%a;7\9DfP{P|P|Q07#IR`Q0X#V'L/LNPhPAP|P|Q0:#k#IRaQ0o'LR6P`PAP|P|Q0~/igR`P^PAP|P|P?PNQ11Q0^#VCePAP|P|PpP6PAP|P|Q0sPaPAP|P|1ihNP`PAA?|p^20C|260D|E@E@E@I0RE@E@E@PBP~b6b7b8X0?X5?X:?X??XB?XM?XN?XAoQ0X,2;?79:A7;T=Q0=/09Q0^96?;Q0@,0L%3U14UP9R>2Q0</0>/OM[[[[[[[^0?^5?^:?^??^B?^M?^N?^AoP4Q0>?7WcPCPDP@Q0iC`Q0ePiQ01Q0mQ0>PcP7P;Q09P\PGP0PdO?b1b2b3b4b@H0SQ1>eO4b>bLWLWEP5P4O2n2001000000121000000bObDbDQ0bPbP:P5P4O3J0@WdWcX;?Q0?Q0HPCPDP@P<PkQ0\PrPGPlPjPCPDP@PdP4Ds#81zC5#8212C:#8211<9#8PCPDP@P1PrP8J0P#8P>P7P8P9P:P5P[PvPyPwQ0`Q0VPzPFQ0zP:PRP5Q0}DfP{P|A?|_hR_AM|hN5W|-00|PA1iNg9M|h9W|_-00|C_PBP~b6b7b8X0?X5?X:?X??1<:99he:Q0f[148P,<99h}9Q0f[[^0?^5?^:?^??P4Pd15H2Q01Q19P8O5b1b2b3b4PCPDP@Q0eQ15P7J0P#8e20Nr7R}P7PCPDP@P<Q14PcPZPkPu11HrRePTP;PlPmQ0UP?PrQ0dQ0dQ0v'<5h4XG?P[PvPyPwPCPDP@Q0hC:R_/bERh%3_Q18/GE#3\x[R_Q0NQ0l'g#jQ0O/gf#j/cz'cPFQ0{Q0}9\R97\5P{P|A?|a^Q12,LaRR9M|^5W|PAP|Q0p9?|RPAP|P|P3PaPAA?|3^RaQ0p9M|^5W|E@FxPBP~b6b7b8X0?X5?X:?P:P5P5P:PWDmQ10125T'010:8P9P8P8P9PTDm[[[^0?^5?^:?P4Pd15HURTPkP8PqQ0YO6b1b2b3b415HeP[PvPyPwPhP_Q0tQ0xP4PkQ0\O2b1b2b3b4P[PvPyPwPhP_Q0rQ0wP4PkQ0ZO2b1b2b3b460=rEoN@0~PCPDP@PcP;DsPkP;O1=AKJQ0]Q0c+0;PCPDP@PcP;I0<1zC;#8'H'H3=Q00PCPDP@PiP=DsPdP=O1=6KJQ0]Q0d+0;PCPDP@PiP=I0<1zC=#8'H'H'HPCPDP@Q0hP>DsP4PCPDP@Q0gP2DsPZPUO1=6KJQ0]00;TPCPDP@Q0kPUI0<1zCU#8'H'H'HP5WEW]P5P4O2n2001000000120000000bOO1WI%8}eO7WbWaW`W_W^X;IPCPDP@PkQ0\PGPlF[eN;0|PGPlPqQ0_P]Q0Y15H4R]P]Q0YPQDmPCPDP@P<PtPu14lPPmPrPnQ0Z,1HRnPQP5PjPYP?Q0ZQ0GQ0G124QRj'<5h4XG?P[PvPyPwPCPDP@PZC:RZ/bER@%3ZQ0D/GE#3\x[RxPzPFQ0SP{P|%VQ,L3R39M|^9W|aRaPAPaC_PBP~b6b7b8X0?X5?1<5j9h45P5P:P:P5PQDm[^0?^5?P415H7PGP8O3b1b2b3b415HnQ0ZP[PvPyPwP@PxQ0tQ0xP4PGPqO2b1b2b3b4P[PvPyPwP@PxPzPFQ0nP{P|P|Q0q-0{3PAQ0uI0RPBP~b6b7b8X0?1<jSQ0y[^0?P4PGQ0_O2b1b2b3b440=EoRGP:PnPQP5PYQ0TPGO6NA0BWCX9IJ0zCuCuCuCuCubtWjWZP5P4O2n2001000000121000000b>bkY05Y04Y03Y02Y01P8P9P:P5P4O5n500000100000015110D10B10C10@10Ab>WnY00WuWvW[P5P4O2n2001000000121000000W>W\P5P4O2n2001000000121000000W>WiP5P4O2n2001000000121000000W>WmP5P4O2n2011000000121000000W>W~P5P4O2n2011000000121000000W>WqWlWxWwWzWyW|W{WfWhWeWYY0?Z0<?XP?Z0=?Z0>?Y09Y08Y0:WpWQWUWWWTWXo"). Qed.

Lemma bd_thru_postd : forall C A' mk m m' (s pp bil : Z), bd_thru mk m bil -> POSTD C A' (s - 48) pp mk m' ->
  live A' (Z_to_bv 64 bil) = Some 104%Z -> (4096 <= bil)%Z -> (bil + 104 < 2 ^ 64)%Z -> (pp = bil + 8 \/ pp = bil + 88)%Z -> bd_thru m' m bil.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilDW ()) ["BilDW"] "h04__x1h17__arithh24__ffh37__sat17h47__sat18h58__varmaph65__with74__x2h84cstrh94__p1h:4__x3h;1zh<2Hah=4__x4h>2A'h?1Ch@2G1hA2G2hB3H1ahC3H2ahD3HpphE2LbhF2PDhG2THhH1ahI3bilhJ1mhK2m'hL2mkhM2nnhN1ohO2pphP1sp;3p;2p;1p;:p;4p;6p;Cp;7p;8g004Hj3yTg00hgj3xTg005Qj3dTg006Zj2\Tg007[j15Tg008@j1UTg008^j1VTg009Aj1KTg01^Uj3PTg00S2j1CTg00P5j16Tg00o;j2OTg0236l:wTg00@ij2GTg009cj4pTg00:fj2jTg00;Hj39Tg00@Mj20Tg00BIj21Tg00l2j2gTg00Bfj2?Tg00AOj2;Tg00Aij1ITg00CBj2LTg00Fhj1QTg01;0j4JTg00PSj1_Tg01;hj2^Tg01<Pj3]Tg00FHj1[Tg00GHj2BTg00Gfj1ZTg00HDj4ATg00Hbj1YTg00I@j1XTg00Ikj2@Tg00;bj1vTg00KUj2uTg00D^j2tTg00L7j2qTg00Lcj3oTg00MBj4nTg00nQj2lTg00JNj2TTg01Ajj3iTg00T7j4=Tg01CZj3hTg001Zj6MTg00OVj1HTg01=4j2<Tg01FRj3>Tg01G;j2NTg025:j1fTg025Xj2kTg0269j3eTg01Ggj3DTg026blCmTg001>j6cTg00XUj3bTg00X1j7WTg00Y\j8aTg00K1j6rTg00Y8j7sTg01HGj7`Tf0R0#5#5p=:f2R1f1R2'1/00p=3g00=aR3/T0p=8Ab320p=4P1g00\CR4g00\bR5P5g00]BR6P3P2g00[\P0C=g00]bR7FWp=2f3R8P4P5P5P6P1P2P0Gap=7P2P4P5P5P6P0P7FWp=EP2P4P5P5P6P0Erp=SP1P4P5P5P6P2P0Fsp=RP1P4P5P5P6P2P0F`p=Fp,2ALR4p,2CLR7p,3ASRR99y47R:3xAd47:R;,\4g00=<R<#5R=#5R>#5R?#5R@#:RA#URB#V%U?#VRC#K[RDf5REf4RF;P0P4P7P:g01J=f8R:f7RG%C<RH#5RI#5#:RJ#6RK,O8P1f6RLPFM:w%K3P4P;P:1GB1Cp%CI#5#:#6RI,j339%:A#:#:#6R;/0811FI%6=RM%6ARA'gRN'?%6?R?,1ERO993L%C=#C#5#:#6RP,1ERQ993L';g00Z@%6@R@=3:2%I2,11RRf9RS/1P'0%5J#6RJ=3S111SI,0R'L';%QC#KRCg01HkRRf?RT1GB8RUP1CJPRf>RV1GBFP8CJ=9C0XNCP4P7P9fAf@f</OKf;PTf=f:RK,GBR9PIP8P1P:PGP3PK100FX;3%_1R7g00[>R4%I1'0RC1^MARW1?4M104A1?4N[[RX104MRYg00>\RZA]MA2UW<RA104N\Z^<YRYg00`1RZ#[R[%QZR\P31B31R]P2%Z3R^CA%Y3R_%X3R`1@3<Ra%8@Rb'41@3=R=52`%v5R5A2`a=C71u`6R6P0P1g00`]Rcg00a=Rd't1q01=9cddAo342CnRdb2b5b6X03X73A30@21021[^03^73P0PGPVPEO3b1b3b4b81lB9R9P7PCPWPXPAPYP[P\1B32RcP_P`%8;=2`aP51T34=2`aC7P6Pdb2b5b6X0310;01042[^03P0PVPKO2b1b3b4b8P7PCPWPXPAPYP[P\PcP_P`P3%8IR4,4aR;g00^BRe%8M=i3BRBC=,E`RMP5P3PaPePBC=,E`C7P6Pdb2b5b6X03110IRe/?NRf1?2N[^03P0PVPSO2Rgb1b3b4b85hKRhEMP3PK%I8=3FeX;3P7PCPWPXPAPYp-0RiP[P\P3P]P21B38R]CAP_P`14a=Rj1@3HRH%8PRk'452`1S`E14H492`jRj5R`5F`P5PjC7P6Pdb2b5b6X03X73X:3W91102Rj111P'0111I,0j,L8';1121Rj118I'0[^03^73^:3^9iP0A3VJGPV%ILR4PGPFO5b1b3b4b8P9PhEMP3PK10eNX;3P7PCPWPXPAPYP[P\PcP_P`PMP5A2`;BC7P6Pdb2b5b6X03A32IN\f^03Pgb1b3b4b8P9PhEMP7PCPWPXPAPYg00Z_RY#HRA#HRX#HRW,<31<3XRX1<3A5>3RA5>3g01K5RC'NR7%HW,<3RW=>3A/NC%f<,k3=e3X1<3Y5>39>3W/NCADZ7[5DZ5DZ5DZP\P3P31B3FP1P^CAP2P]CAP_P`14=HRH1@3>R>/4kRk52`%8J,4>=2`=1S`L5R`5F`P5P`14>b=2`=P5P`P3Pag00a]Rb%8?R_,4>C=,E`P3PaPbPkC=,E`5F`P514a_=2`=A2`Ha5F`C7C7C7P6Pdb2b5b6X03X73X:3X=3X9i118P,0jA38J2/LF';A3F@1A931OA931Q';A38?FA3FE8';[[[^03^73^:3^=3^9iP011VI93G4PVP4PGPTPFPEP:O8b1b3b4b8MCmPRPVPUP1CJPSP8P1P2P0O4EcWCWBWMXH3APSKLeWDWAW@WEWFWGXI3XO3XP3XKDXJDWLW>W?o"). Qed.

(* [comment removed for export] *)
Lemma pixa_cells_keep : forall (m m' : word -> option byte) pa parr ba barr n,
  pixa_cells m pa parr ba barr n ->
  (forall a nn, (pa <= a)%Z -> (a + Z.of_nat nn <= pa + 32)%Z -> rdn SEGS m' (Z_to_bv 64 a) nn = rdn SEGS m (Z_to_bv 64 a) nn) ->
  (forall a nn, (ba <= a)%Z -> (a + Z.of_nat nn <= ba + 24)%Z -> rdn SEGS m' (Z_to_bv 64 a) nn = rdn SEGS m (Z_to_bv 64 a) nn) ->
  pixa_cells m' pa parr ba barr n.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilDW ()) ["BilDW"] "h04__x1h17__arithh24__ffh38__varmaph45__with51Hh61oh71xh81ah91mh:1nh;2nnh<2C1h=2C2h>2C3h?2C4h@2C5hA2C6hB2C7hC2C8hD2C9hE2KbhF2KphG2PChH2bahI4barrhJ2m'hK2pahL4parrhM1yp%0p;1p;6p;2p;3p;4p;7p;<p;Bg007[j1=Tg008@j1XTg008^j1STg009Aj1QTg027dj6<Tg00@MR0j22Tg00AiR1j1MTg00BIR2j20Tg00P5j1FTg00Fhj1RTg00@ij26Tg00S2j1YTg00;Hj34Tg00OVj1ETg028gj2ITg00CBR3j2:Tg00FHj1_Tg00GHj2^Tg00Hbj1]Tg00I@j1\Tg00Ikj2[Tg00JNj2HTg00KUj2ZTg00D^j2PTg00L7j2mTg00Lcj3lTg00MBj4kTg00C]j1jTg00D;j4iTg00Qcj4DTg01;0j4@Tg00:fj2OTg00XUj3gTg00T7j4fTg00X1j7eTg00VAl<dTg00VflBcTg00WLl<bTg00Q8j4hTg001Zj6aTg01HkR4f2R5f1R6f0R7C@p=8f4R8P4f3R9P5P6C@;47p=Gg00[>R:,07,66p=Jf6R;P4f5R<P8P9C@1I67,O534p=V1I67,O5p=3P4P<1095,68P6C@=4;7p=5f7R=P4P;1089,6<P5C@;46/:7p=1P4P<109:,68P5C@=4;6/:7p=BP4P81056,69P7C@p=UA4;<8A4956/:7':p=T1067,65p=LA4=;<P4P9P5P6C@=487':p=`107:p=N1O679495p=Kg00=aR>?g67p=;P5g00\Cg00\bR?P?g00]BR?P>P6g00[\P7Cfg00]bFep=91P>7p=7g00Z@R@P>P>P>P1P1P<P8P9P5P6P7M<dp=WP>P>P>P>P>P>P2P7P6P5P2P9P8P<P;P=f8R2f9R1MBcp=>P>P>P0P=P0P;P<P8P9P5P6P7M<bp=?P81295P6P7Chp=AP=P4P;P<P8C@P9P5P6P7Eap=Cg00=<R4#=R0#=RA#=RB#=RC#=RD#=#XRE#S%XB#SRF#Q[RGP;P8P9P5P6P7E<12=6%M6,05RH%FDRD,02'2%RFRF#QRIf:RJ16E9RKP5f;RL?8K5RMDG[[^;@^8>12;6%Y4#=#=#=#FRN,0=,2Hf<RH?8K594IM[[^;@^8>P5P1P=P;P<P8P9E<P3PIPJ1JE2g00Z_#E#E#E#ER9PFP9P8FVPIPJPEP2%FARAP9%Y0#=#F93F9R0PIPJPEP2%FBRBP9%F493F9R8PIPJPEP2%FCRC%E9#E#E#ERMA3FM=PIPJPEP2PNPMA3FM;PIPJPEP;P9A3F9:RKPIPJPEP;PAP9P0PIPJPEP;PBP9P8PIPJPEP;PCPMA3FM<F5G1G1FBG1G1G1G1PJP1P2P=P;P<E<P7PIPH1JEJR=P9PFP9P;FVPIf=R;PEPLPAP9P0PIP;PEPLPBP9P8PIP;PEPLPCPMA3FMJROPIP;PEPLPNPMA3FM1RPPIP;PEP1P9PKPIP;PEP1PAP9P0PIP;PEP1PBP9P8PIP;PEP1PCPMA3FM2F5G1G1FBG1G1G1G1P3PIf>R2PEPHPAP9P0F5PIP2PEPHPBP9P8PIP2PEPHPCPMA3FMLPIP2PEPHPNPMPOPIA82=9PKPIP2PEPJPAP9DUP0PIP2PEPJPBP9P8PIP2PEPJPCPMPPF5G1FTG1G1G1P2P;PHPLPJP1E<P7PIf@RJALE2ARLP9P0DGPIfARPPEf?R=PBP9P8PIPPPEP=PCPMA3FM2ROPIPPPEP=PNPMA3FM;RQPIPPPEP;P9PKPIPPPEP;PAP9P0PIPPPEP;PBP9P8PIPPPEP;PCPMA3FMHF5G1G1FBG1G1G1P3PIfBRHPEPJPBP9P8F5PIPHPEPJPCPMA3FM=PIPHPEPJPNPMPOPIPHPEP2P9PKPIA8HL9P0PIPHPEP2PBP9DUP8PIPHPEP2PCPMPQF5FTFBG1G1PHPPPJP=P2P;E<P7PIfDR2ALEHBR=P9P8DGPIfERQPEfCRLPCPMA3FMHROPIPQPEPLPNPMA3FMPRRPIPQPEPPP9PKPIPQPEPPPAP9P0PIPQPEPPPBP9P8PIPQPEPPPCPMA3FMJF5G1G1FBG1G1P3PIfFRJPEP2PCPMA3FMLF5PIPJPEP2PNPMPOPIPJPEPHP9PKPIPJPEPHPAP9P0PIA8J=9P8PIPJALEHCPMPRG`G1FBG1PJPQP2PLPHPPE<P7PIfHRHALEJCRLPMA3FMQRRDGPIfIR=PEfGROPNPMPRPIP=PEPQP9PKPIP=PEPQPAP9P0PIP=PEPQPBP9P8PIP=PEPQPCPMA3FM2F5G1G1FBG1P3PIfJR2PEPHPNPMA3FMJF5PIP2PEPJP9PKPIP2PEPJPAP9P0PIP2PEPJPBP9P8PIP2PLPMPRDGG1G1FBP2P=PHPOPJPQE<P7PIfLRJPEP2PNPMA3FMHRHF5PIfMROPEP=P9PKPIPOPEP=PAP9P0PIPOPEP=PBP9P8PIPOPEP=PCPMPHF5G1G1FBP3PIfNRH1JE2P9PKDGPIPHPEP2PAP9P0PIPHPEP2PBP9P8PIPHPEP2PCPMA3FM=F5G1G1PHPOPJfKP2P=E<P7PIfPR21JEJP9PKDGPIfQRRPEPOPAP9P0PIPRPEPOPBP9P8PIPRPEPOPCPMA3FMJF5G1G1P3PIfRRJPEPHPAP9P0F5PIPJPEPHPBP9P8PIPJPEPHPCPMA3FMOF5G1PJPRP2fOPHPOE<P7PIfTRHPEP2PAP9P0F5PIfURLPEPRPBP9P8PIPLPEPRPCPMA3FM2F5G1P3PIfVR3PEPJPBP9P8F5PIP3PEPJPCPMA3FMRF5P3PLPHfSPJPRE<P7PIfXR2PEPHPBP9P8F5PIfYRSPEPLPCPMA3FMHF5PI%N2RT,6ERU=8S9RVPF1I9HCK102ARW,6ERX=8S9RY=4I0RZ102BR[,6ER\=8S9R]=4I8R^102CR_,6ER`=8SMRafWRb93FMRc54IRd102NRe,6ES00=8SMS01A3FM3Rf54IS02%N3Rg,6ES03=8S9S04=4IKS05103ARh,6ES06=8S9S07=4I0S08103BRi,6ES09=8S9S0:=4I8S0;PI103CRj,6ES0<=8SMS0=PF1IMLCKS0>':S0?':S0@':RE':Rk':Rl':Rm':PIfZRnPUP9PIP7PF1I9LCKX6IPOPVPJPTP9g00`1RV#_RO%RVRV1^>6RU%]>Ro%\>Rp1[>4R41H>:,;4Rq391Zp?R?P7P5g00`]Rrg00a=Rs'P1m75=4rsdAl>:6CkR:b2b3b4X0>Rs%N7Rr,27^0>R5P7PSO1Rtb1122Te%M9Ru,0TRv102DRw'2Rx10TARyPwP7X7>Rz1267#jXM>X7>R{PvPyPzPzPzP>P>g00_M1067Ci#7X9>X:>RyPTPT%7TPuPAPzPz%M7#7X7@R@P9PA%7AEWRTM:>PwPw%7wRvG?POPVPUPo1H>AR|,;qRq1H>D,;4R}59pP?P:b2b3b4X0>10rARr107DRD'2^0>Ptb1DAPxeO4GCPZPmPIPnPXP9A4I70X6IR0P=PYPJPWP9POPVPUPo1;4|RY99p4P?P:b2b3b4X0>R=107ARX,27^0>RmPtb1122We10WuRZ/2wRx10WAR~PwPzP{PZP~PzPzPzPyPWPW%7WPuPAPTM:>PwPwPvG?POPVPUPo1;Y|RY=9p}P?P:b2b3b4X0>10XARX/2D^0>Ptb1DAPxeO4GCP^PlPIPnP\P9A4I78X6IR8PQP]PJP[P9POPVPUPo1H>BR],;4RQ99p4P?P:b2b3b4X0>R\107BRl,27^0>R^Ptb1122[e10[uRx/2wRW10[AR~PwPzP{PxP~PzPzPzPyP[P[%7[PuPAPTM:>PwPwPvG?POPVPUPo1;Q|RQ=9p}P?P:b2b3b4X0>10lARl/2D^0>Ptb1DAPWeO4GCPdPkPIPnP`PMPIP7PF1IM2CKX6IPPPaPJP_PMPOPVPUPo1H>C,;4Ra99p4P?P:b2b3b4X0>RP107CRC,27^0>RFPtb1122_e%MMR`,0_Rk/2wRd10_BRWPwPzP{PkPWPzPzPzPyP_P_%7_P`PBPzPzP@PMPB%7BEWR@M:>PwPwPvG?POPVPUPo1;a]Ra=9p}P?P:b2b3b4X0>10CBRC/2D^0>Ptb1DAPdeO4GCQ02PEPIPnQ00PMA4I7cX6IP;Q01PJPePMPOPVPUPo1H>N,;4RJ99p4P?P:b2b3b4X0>107NR4,27^0>Ptb1122ee10e`R;/2wRc10eBREPwPzP{P;PEPzPzPzPyPePe%7eP`PBP@M:>PwPwPvG?POPVPUPo1;J]=9p}P?P:b2b3b4X0>104B/2D^0>Ptb1DAPceO4GCQ05Q0@PIPnQ03P9A4I7KX6IP1Q04PRPgP9PsP5P7PbO1R5b1123ge10guRs103NRN'2R110gARKPNPzP{PsPKPzPzPzPyPgPg%7gPuPAPTM:>PNPN%7NRgG?POPVPUPoA9pqJP?P:b2b3b4X0>12r4^0>P5b1DAP1eO4GCQ08Q0?PIPnQ06P9P0P<Q07PRPhP9P=PmP5b1123he10huRm/2NR=10hAR<PNPzP{PmP<PzPzPzPyPhPh%7hPuPAPTM:>PNPNPgG?POPVPUPoA9pYJP?P:b2b3b4X0>12X4^0>P5b1DAP=eO4GCQ0;Q0>PIPnQ09P9P8P6Q0:PRPiP9P\P^P5b1123ie10iuR^/2NR\10iAR9PNPzP{P^P9PzPzPzPyPiPi%7iPuPAPTM:>PNPNPgG?POPVPUPoA9pQJP?P:b2b3b4X0>12l4^0>P5b1DAP\eO4GCPIPnQ0<PMA4I7fX6IP7Q0=PRPjPMPPPFP5b1123je10j`RF/2NRP10jBRMPNPzP{PFPMPzPzPzPyPjPj%7jP`PBP@M:>PNPNPgG?POPVPUPoA9paJP?P:b2b3b4X0>12C4^0>P5b1DAPPeO4GCCDCDCDCDCDCDCDCDPSP2PbP3PLPHE<eWDWCP6P7O2n2001000000121000000W5WBP6P7O2n2001000000121000000W5WAP6P7O2n2001000000121000000W5W@P6P7O2n2011000000121000000W5W?P6P7O2n2011000000121000000W5W>P6P7O2n2011000000121000000W5W=P6P7O2n2011000000121000000W5W<P6P7O2n2011000000121000000b5WEWFWGX:>XI>XH>XL>XK>XJGW9o"). Qed.

(* [comment removed for export] *)
Lemma FRM_byte_above : forall C s m m' (a : word), Cok C -> FRM C s m m' -> (s <= u a)%Z -> (c_top C - LSTK <= s)%Z -> m' a = m a.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptBilDW ()) ["BilDW"] "p'0h04__x1h14__x2h24__p1h34__x3h44__x4h54__x5h62Hah77__arithh84__ffh97__sat17h:7__sat18h;7__sat19h<7__sat20h=7__sat21h>8__varmaph?5__with@4__x6hA1GhB4__p2hC4__p3hD1ChE2CKhF1FhG1HhH3HlohI3PINhJ4PIN0hK4PIN1hL4PIN2hM4PIN3hN4PIN4hO4PIN5hP4PIN6hQ4PIN7hR4PIN8hS2T1hT2T2hU2T3hV2T4hW2T5hX1ahY1mhZ2m'h[1sh\1zi005ck_ali016ck_imgi026ck_sp0i038ck_sp0hii046ck_topp%0p&0p;3p;1p;5p;8p;2p;4p;6p;7g004Hk30ITg00hgk30HTg007[j11Tg008@j1jTg008^j1hTg009Ak10=Tg00ilR0j5`Tg01EPk800Tg00nQj2GTg00@Mj20Tg01NXj4>Tg00o;j2OTg00;Hj3ITg01>ej4VTg016Aj1UTg00P5j15Tg00BIj27Tg01P_j4cTg014cj2YTg01Qck105Tg029dk303Tg00S2j16Tg00l2j2aTg02:lj3wTg02<5j1vTg02=9j3rTg02>Bj1qTg02?Fj3oTg02@Oj1nTg02ASj3mTg02B_j1lTg02Cfj1kTg00Bfj2:Tg0212j2ETg00<cj19Tg00CBj24Tg02Dmk30GTg02F5j3iTg02FPk30FTg02Fkk30ETg02H5k10CTg02I>k30?Tg01;hj2gTg01<Pj3fTg01U[j2eTg00OVj1HTg01=4j2dTg01G;j2ZTg00FHk10<Tg01Ggj3\Tg00Fhk10;Tg00GHj2MTg00Gfk109Tg00Hbk107Tg00I@k106Tg00JNj2PTg00T7j4JTg00;bk104Tg00Ikj2_Tg01VLj3^Tg00KUj2~Tg00D^j2{Tg00L7j2|Tg00Lcj3}Tg00MBj4zTg02JIk601Tg01k\k202Tg02KUj5yTg01l]j2xTg02L\k508Tg01mak20:Tg01nej6uTg01Rhj3tTg02Mdk30>Tg01FRj3sTg00HDk40@Tg00X1j7]Tg00XUk30ATg00Y\j8RTg00K1k60BTg00Y8j7pTg00Tbk60DTf0R1#1#1p=N%11#1#1#1p=[%11#1#1#1#1#1#1#1p=Tg00=aR2?t21p=LB0>221p=Kg00[>R3/01p=3f2R4f1R5/01'4p=X1045/41p=81d21p=DAs251p=FP2P4P5P1H0@p=21_21p=?P5g00\CR6g00\bR7P7g00]BR8P1g00]bR9F]p=AP4P6P7P7P8P2P5g00[\R:P1CJP9F]p=<B0A251p==P2P5P:P1CJp=@f6R:P6P7P7P8f5R;f4R<f3R=P6P7P7P8P4P5P1GRGRp=CP<P6P7P7P8P=P6P7P7P8P4P9F]P5P1GRp=;P5P6P7P7P8P1J0Bp=QP2P5g00^BP1CJp=SP4P6P7P7P8P5P1Fpp=BP=P6P7P7P8P4P5P1GRp=WP5P6P7P7P8P1J0Dp=bp,2ALR6p,2CLR9p,3ASR:0I69R>40Hg00=<R?#1R@#1RA#1RB#1RC#NRD#jRE#hS00%jB#h$0=RF[S01Q01Q00P6P9P>g01J=RGP<D`P6P9P>PGP;P<P=P4L001GE4,0;P6P9P>f7RHC>g01\KRI'O/0:P=P6P9P>PGf8RJD`P0P6P9P>PGf9R0PHP:O1PJP:O15IFP1P6P9P>f>S02CV#U%1D#N#[RK#5RL'7/7IP6P9P>Q02C>'0P6P9P>f?RMC>P6P9P>PMCc,GE'0P6P9P>f@S03Cc,GE%1KRK#NRN#1#N#[#T#T#T#5'0P6P9P>fAC>%5CRC'Y=I23&05GRO#LRPP6P9P>fBS04CV#U'0p,4PINSRQ:036G%KORO#3?XOP%5@RR%6@RS#1#N#5RT'aRU7XPAw6GQ%vGRV#K%LVRW/0P58OAr6GQ%qGRX#KRY%LX/0P58OAo6GQ%nGRZ#KR[%LZS05/0P58OAm6GQ%lGR\#KR]%L\S06/0P58O%kGR^,0ORO%5BRB,7^R_/0PRP1:1_98^11EV5#91EX5#91EZ5#91E\5#9'4'4'4[^\2RX'4RVB0G6GQR_3iPOB0FOV_9iPXPPB0E6GQ&0CGRP#3%5DRD,aRRX,:P'4g01]N%5KRK9I2IB0?6GQ10W]98W[98WY98W^fGfIRWP6P9P>fMRYPW1gRTRP1:3RR_%3T1:3U[[RV%3RROg00>\R`AfRT5UW6RT%3U\`^6ORU1gRDRa%3D1:3X[\_R_AfRD5V`X6ORD%3X\`^6OROP6P9P>fQR`C>RX/eCS07%3X%3CRXP6P9P>fSRRC>Rb/YC#3[[S08g00`1Rcg00Z_Rd#HRe#HRf#HRg#D%Df%De1d2d'F'F'FRdg01K5Re'Z&0<cRf3\&0;cRh1M2<Ri&092Rj724Rk1M2;Rl?2=jRm725&072Rn&062RoP2%?SRSg00a]S091P2KRpCJ,AoS0:&047R7Po%6?#6#1#6#6#6#[#T#5Rq,P2Rr1_2?Rs5<oP7PoPo1P2LRt,=s/=S%?ARA'@P7PoA^2AS%6?R?#?Ru5<oS0;P7Po%?@R@9<ouS0<P7A<os@S0=FCD;FC1~o8R8P1P4g00`]Rvg00a=Rw'{1|14=IvwdA}235CzR3b8b>b?X02X12X32X42X52AI2<KRK10q5174L/7:/0;1O:H/0;10:;10;:[[[[[^02^12^32^42^52P1PIPbfRRwfO,GERvP6P9P>PRCV#US0>PHQ03fDS0?fKRRfLRxO:b7b9b:b;b<b=J012026WRyP6PGPQfJRzP1Dy1GEzR{,EZPPPVPTPUPaP_PDPO1ebCS0@%3bP6P9P>fUS0AC>RZ/YC#3\X[S0Bp-0RX%HgRg#HRC#H#D%Dg/FdRd'F/Ze=\cfS0CPh1M2:Rg92j;?2=j92k5PnPo1QoJR|%1?R}#6#?R~,S@,Ao5BoP7PoP2PAQ09PpCJ,AoS09P7Po1Qo0RpA<o~r5BoP7PoPo1@rSP7PoPo1=St/=A/@uP7PoPoA^2uA/@sP7PoQ0=P7f:,QoCWD;D;D;S0=CWFCP8P3b8b>b?X02X12X32X42X52X@2X2XXBXWC1:5;,4:AX0Hq10qHR~17JL/7H/0:RL1OHJRJ/0;10:HPM[[[[[\K[^02^12^32^42^52^@2^2X^BX^CXS0DP1g00>?RM%5NRN/0[1GE`R`,0[Q05P6P9P>Q0ACV#US0APIPZP`fTR[P:P0Q02Q04fFREPYfNR;O@b7b9b:b;b<b=bAWA%9ye1x6WRyP6PGPQPzP1I081E\{PPPVPTPUPaP_PDPOQ0@Q0BQ0CPhA2j:g92l=92k5PnPo%6?#6#?R?,S@,Ao9Bo|P7PoQ09P7PoA<o?r9BopP7Q0=CWFCP8P3b8b>b?X02X12X32X42X52X@2X2XXBXXCXQ0DP1PM10N]10]`Q06Q0APIPZP`P[P:P0f=Q04PEPYP;O@b7b9b:b;b<b=bAWA%9yePPPVPTPUPaP_PDPOQ07Q08%DC/Fd/Ze=\cfPhA2i4g?25mPnPoQ0:P7Po1P2B,=sRs=<orP7PoPo%?}R},@rP7PoPo1=}t/=S/@AP7PoQ0;P7PoQ0<P71S@s,Ao9Bo|,boFCD;D;FCP8P3b8b>b?X02X12X32X42X52X@2X2X175B/0q10J:10H:f<17:B,:H'4PM[[[\L\~[\K^02^12^32^42^52^@2^2XP110^vQ0>PIPbPwPvP^PHP0Q03Q0?PRPxO=b7b9b:b;b<b=20:GW#9ePPPVPTPUPaP_PDPOQ07Q08PfPh1M24?24j1M25724PnPoPo1@AuP71Qo<1SuA,Ao5Bo,boD;P8P3b8b>b?X02X12X2X10511:54,4=PM[[^02^12^2XP11ObI/0vPwPvPxO4b7b9b:b;b<b=P6P9P>PYPxPWEu#9eO6PzPWO1PRPWO15IFebRbQbPbObNbMbLbKbJbIWWWVWUWTWSP<P=P4P5P1O5n5000001000000151104102103100101bGWHW6WFWEWXWZWYX[2WDo"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bld_loop_W : forall (n : nat) C Ae A (m0 m : word -> option byte) md vme regs regs0 (s bil ls h i : Z) (linesf : Z -> Z) (S : TSet),
  Z.of_nat n = (10 - i)%Z -> (0 <= i < 10)%Z -> Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 9 = Z_to_bv 64 bil ->
  getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i -> (forall r, In r bd_rest -> getr regs r = getr regs0 r) ->
  (4096 <= bil)%Z -> (bil + 104 <= s - 48)%Z -> live A (Z_to_bv 64 bil) = Some 104%Z ->
  (4096 <= ls)%Z -> (ls + 80 <= s - 48)%Z -> live A (Z_to_bv 64 ls) = Some 80%Z -> (1 <= h)%Z ->
  rdn SEGS m0 (Z_to_bv 64 (bil + 56)) 4 = Some (Z_to_le_bytes 4 10) -> rdn SEGS m0 (Z_to_bv 64 (bil + 96)) 8 = Some (Z_to_le_bytes 8 ls) ->
  (forall k, (0 <= k < 10)%Z -> (0 <= linesf k < 2 ^ 64)%Z /\ live (c_A0 C) (Z_to_bv 64 (linesf k)) = None /\ linesf k <> bil /\ linesf k <> ls /\
                               rdn SEGS m0 (Z_to_bv 64 (ls + 8 * k)) 8 = Some (Z_to_le_bytes 8 (linesf k))) ->
  (forall k k', (0 <= k < k')%Z -> (k' < 10)%Z -> linesf k <> linesf k') ->
  (forall k, (i <= k < 10)%Z -> live A (Z_to_bv 64 (linesf k)) = Some (8 * h)%Z) ->
  (forall k, (0 <= k < i)%Z -> live A (Z_to_bv 64 (linesf k)) = None) ->
  (forall q, (forall k, (0 <= k < i)%Z -> q <> Z_to_bv 64 (linesf k)) -> live A q = live Ae q) ->
  POSTM C A (s - 48) m0 m -> roomtr Ae vme A (m_vmmaps md) 0 0 ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) ->
     getr regs' 2 = Z_to_bv 64 (s - 48) -> getr regs' 4 = Z_to_bv 64 352880 -> getr regs' 9 = Z_to_bv 64 bil -> (forall r, In r bd_rest -> getr regs' r = getr regs0 r) ->
     (forall k, (0 <= k < 10)%Z -> live A' (Z_to_bv 64 (linesf k)) = None) ->
     (forall q, (forall k, (0 <= k < 10)%Z -> q <> Z_to_bv 64 (linesf k)) -> live A' q = live Ae q) ->
     POSTM C A' (s - 48) m0 m' -> roomtr Ae vme A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' (Z_to_bv 64 240420) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 240352) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros C Ae A m0 m md vme regs regs0 s bil ls h i linesf S
    Hn Hi CK HW Hs16 Hlo Hhi E2 E4 E9 E18 E19 ER Hbil Hbils Lbil Hls Hlss Lls Hh R56 R96 LF DIST LIVE FREED LEQ PM RT HK.
  { lia. }
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as HLS. unfold ALLOC_STACK in Hlo. unfold bd_rest in ER.
  destruct (LF i Hi) as (Glf & L0lf & NEbl & NElsl & Rlf).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lls) as (_ & ALls & _). rewrite u_Z2bv in ALls by lia.
  assert (Llf : live A (Z_to_bv 64 (linesf i)) = Some (8 * h)%Z) by (apply LIVE; lia).
  assert (R96m : rdn SEGS m (Z_to_bv 64 (bil + 96)) 8 = Some (Z_to_le_bytes 8 ls))
    by (rewrite (LIVK_rdn SEGS A m0 m (Z_to_bv 64 bil) 104 (bil + 96) 8 (proj2 PM) Lbil)
          by (rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact R96).
  assert (Rlfm : rdn SEGS m (Z_to_bv 64 (ls + 8 * i)) 8 = Some (Z_to_le_bytes 8 (linesf i)))
    by (rewrite (LIVK_rdn SEGS A m0 m (Z_to_bv 64 ls) 80 (ls + 8 * i) 8 (proj2 PM) Lls)
          by (rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Rlf).
  destruct (bl_Lb al_rom fx regs m s bil ls i (linesf i) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (al16_mod8 _ ALls) ltac:(lia) Glf
              R96m Rlfm E2 E9 E18)
    as (fin1 & RUN1 & r1 & M1 & -> & -> & Q1 & Q2 & Q9 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (Q4 : getr r1 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  apply (W_free16 C A m md r1 (Z_to_bv 64 (linesf i)) (Z_to_bv 64 240404) (8 * h) (s - 48) S CK HW Q10 Llf L0lf Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r2 HW2 CS2 Llf2 LEQ2 PM2 RT2.
  assert (SUB : sub_live A2 A)
    by (intros q k Hq; pose proof (live_neq A2 q _ k Hq Llf2) as NE; rewrite <- (LEQ2 q NE); exact Hq).
  assert (PM' : POSTM C A2 (s - 48) m0 m2)
    by (eapply POSTM_trans; [apply (POSTM_sub C A2 A); [exact SUB | exact PM] | exact PM2]).
  assert (RT' : roomtr Ae vme A2 vm2 0 0) by exact (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT RT2 ltac:(lia) ltac:(lia)).
  assert (NEbil : Z_to_bv 64 bil <> Z_to_bv 64 (linesf i)) by (apply zneq_w; lia).
  assert (NEls : Z_to_bv 64 ls <> Z_to_bv 64 (linesf i)) by (apply zneq_w; lia).
  assert (Lbil2 : live A2 (Z_to_bv 64 bil) = Some 104%Z) by (rewrite (LEQ2 _ NEbil); exact Lbil).
  assert (Lls2 : live A2 (Z_to_bv 64 ls) = Some 80%Z) by (rewrite (LEQ2 _ NEls); exact Lls).
  assert (R56m : rdn SEGS m2 (Z_to_bv 64 (bil + 56)) 4 = Some (Z_to_le_bytes 4 10))
    by (rewrite (LIVK_rdn SEGS A2 m0 m2 (Z_to_bv 64 bil) 104 (bil + 56) 4 (proj2 PM') Lbil2)
          by (rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact R56).
  assert (V2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (V9 : getr r2 9 = Z_to_bv 64 bil) by (csr; reflexivity).
  assert (V18 : getr r2 18 = Z_to_bv 64 (8 * i)) by (csr; reflexivity).
  assert (V19 : getr r2 19 = Z_to_bv 64 i) by (csr; reflexivity).
  assert (H40 : getr regs0 4 = Z_to_bv 64 352880) by (rewrite <- (ER 4%bv) by in_lit; exact E4).
  destruct (Z.eq_dec i 9) as [->|Hi9].
  - destruct (bl_Hl al_rom fx r2 m2 s bil ltac:(lia) ltac:(lia) ltac:(lia) R56m V2 V9 ltac:(rewrite V18; reflexivity) V19)
      as (fin3 & RUN3 & r3 & M3 & -> & -> & P2 & P9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    apply (HK A2 m2 vm2 r3 HW2 P2).
    + csr; reflexivity.
    + exact P9.
    + intros r Hr; unfold bd_rest in Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [csr; reflexivity|]); destruct Hr.
    + intros k Hk. destruct (Z.eq_dec k 9) as [->|Hk9]; [exact Llf2|].
      assert (NEk : Z_to_bv 64 (linesf k) <> Z_to_bv 64 (linesf 9%Z))
        by (destruct (LF k ltac:(lia)) as (Gk & _); apply zneq_w; [lia | lia | apply DIST; lia]).
      rewrite (LEQ2 _ NEk). apply FREED. lia.
    + intros q Nq. rewrite (LEQ2 q (Nq 9%Z ltac:(lia))). apply LEQ. intros k Hk. apply Nq. lia.
    + exact PM'.
    + exact RT'.
  - destruct (bl_Hm al_rom fx r2 m2 s bil i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R56m V2 V9 V18 V19)
      as (fin3 & RUN3 & r3 & M3 & -> & -> & P2 & P9 & P18 & P19 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    assert (ER3 : forall r, In r bd_rest -> getr r3 r = getr regs0 r)
      by (intros r Hr; unfold bd_rest in Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [csr; reflexivity|]); destruct Hr).
    assert (LIVE2 : forall k, (i + 1 <= k < 10)%Z -> live A2 (Z_to_bv 64 (linesf k)) = Some (8 * h)%Z).
    { intros k Hk.
      assert (NEk : Z_to_bv 64 (linesf k) <> Z_to_bv 64 (linesf i))
        by (destruct (LF k ltac:(lia)) as (Gk & _); apply zneq_w; [lia | lia | apply not_eq_sym; apply DIST; lia]).
      rewrite (LEQ2 _ NEk). apply LIVE. lia. }
    assert (FREED2 : forall k, (0 <= k < i + 1)%Z -> live A2 (Z_to_bv 64 (linesf k)) = None).
    { intros k Hk. destruct (Z.eq_dec k i) as [->|Hki]; [exact Llf2|].
      assert (NEk : Z_to_bv 64 (linesf k) <> Z_to_bv 64 (linesf i))
        by (destruct (LF k ltac:(lia)) as (Gk & _); apply zneq_w; [lia | lia | apply DIST; lia]).
      rewrite (LEQ2 _ NEk). apply FREED. lia. }
    assert (LEQ3 : forall q, (forall k, (0 <= k < i + 1)%Z -> q <> Z_to_bv 64 (linesf k)) -> live A2 q = live Ae q).
    { intros q Nq. rewrite (LEQ2 q (Nq i ltac:(lia))). apply LEQ. intros k Hk. apply Nq. lia. }
    apply (IH C Ae A2 m0 m2 (with_vmmaps vm2 md) vme r3 regs0 s bil ls h (i + 1)%Z linesf S ltac:(lia) ltac:(lia) CK HW2 Hs16
             ltac:(unfold ALLOC_STACK; lia) Hhi P2 ltac:(csr; reflexivity) P9 P18 P19 ER3 Hbil Hbils Lbil2 Hls Hlss Lls2 Hh R56 R96 LF DIST
             LIVE2 FREED2 LEQ3 PM' ltac:(rewrite with_vmmaps_vmmaps; exact RT')).
    intros A' m' vm' regs' HW'. rewrite with_vmmaps_twice in HW' |- *. exact (HK A' m' vm' regs' HW').
Qed.

Ltac bd_fld FLD c H :=
  pose proof (FLD c ltac:(cbn [bc_bl2 app In]; repeat (first [left; reflexivity | right]))) as H; cbn [c_off c_len c_val fst snd] in H.

Lemma bd_init : forall C A m md M1 m1 (s bil pixs : Z) v,
  Cok C -> W C A m md -> (c_top C - LSTK + 80 <= s)%Z -> (s <= c_top C)%Z ->
  live A (Z_to_bv 64 bil) = Some 104%Z -> live A (Z_to_bv 64 pixs) = Some 64%Z -> pixs <> bil ->
  (0 <= bil < 2 ^ 64)%Z -> (0 <= pixs < 2 ^ 64)%Z ->
  rinv [((s - 40)%Z, 40%Z)] m M1 -> FRM C s m M1 ->
  (forall x : word, (u x < s - 48 - 32 \/ s - 48 <= u x)%Z -> ~ (pixs + 20 <= u x < pixs + 24)%Z -> ~ inslot bil x -> m1 x = M1 x) ->
  PIXat m1 pixs v ->
  bd_keep C A A m M1 m1 s bil pixs v /\
  (forall a nn, (bil + 8 <= a)%Z -> (a + Z.of_nat nn <= bil + 104)%Z -> rdn SEGS m1 (Z_to_bv 64 a) nn = rdn SEGS m (Z_to_bv 64 a) nn).
Proof.
  intros C A m md M1 m1 s bil pixs v CK HW Hlo Hhi Lb Lp NE Gb Gp RI FR K1 PX.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as HLS.
  destruct (exW_blk_rng C A m md bil 104 CK HW Lb Gb ltac:(lia)) as (Bb1 & Bb2 & Bb3).
  destruct (exW_blk_rng C A m md pixs 64 CK HW Lp Gp ltac:(lia)) as (Bp1 & Bp2 & Bp3).
  pose proof (exW_blk_apart C A m md bil pixs 104 64 CK HW Lb Lp (not_eq_sym NE) Gb Gp ltac:(lia) ltac:(lia)) as AP.
  assert (MX : forall x : word, (u x < s - 80)%Z -> M1 x = m x).
  { intros x Hx. apply (proj2 RI). intros r Hr. destruct Hr as [<-|[]]. unfold inreg. cbn [fst snd]. lia. }
  split.
  - refine (conj (sub_live_refl A) (conj Lp (conj _ (conj _ (conj _ PX))))).
    + intros q k x Lq NEq Hx NR.
      assert (Hk : (0 < k)%Z) by lia.
      destruct (blk_range C A m md q k CK HW Lq Hk) as [Bq1 Bq2].
      assert (Eq : Z_to_bv 64 (u q) = q) by apply Z_to_bv_bv_unsigned.
      assert (NEq' : u q <> bil) by (intros E; apply NEq; rewrite <- Eq, E; reflexivity).
      assert (Lq' : live A (Z_to_bv 64 (u q)) = Some k) by (rewrite Eq; exact Lq).
      pose proof (exW_blk_apart C A m md (u q) bil k 104 CK HW Lq' Lb NEq' ltac:(lia) Gb ltac:(lia) ltac:(lia)) as APq.
      rewrite (K1 x ltac:(lia) NR ltac:(unfold inslot; lia)). apply MX. lia.
    + intros a Ha1 Ha2.
      apply rdn_ext; rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; [lia|].
      intros x Hx. apply K1; [lia | lia | unfold inslot; lia].
    + apply (FRM_trans C s m M1 m1 FR). intros a NG NGl NEr NH NS. unfold scratch in NS.
      apply K1.
      * lia.
      * intros Hr. apply NG. exact (proj1 (blk_byte C A m md (Z_to_bv 64 pixs) 64 a CK HW Lp ltac:(rewrite u_Z2bv by lia; lia))).
      * intros Hs. unfold inslot in Hs. apply NG. exact (proj1 (blk_byte C A m md (Z_to_bv 64 bil) 104 a CK HW Lb ltac:(rewrite u_Z2bv by lia; lia))).
  - intros a nn Ha Hb.
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
    intros x Hx. rewrite (K1 x ltac:(lia) ltac:(lia) ltac:(unfold inslot; lia)). apply MX. lia.
Qed.

Lemma not_gone_7 : forall (A7 : AS) pa parr ba barr (pixes datad : Z -> Z) (q : word) k,
  live A7 q = Some k -> live A7 (Z_to_bv 64 pa) = None -> live A7 (Z_to_bv 64 parr) = None ->
  live A7 (Z_to_bv 64 ba) = None -> live A7 (Z_to_bv 64 barr) = None ->
  (forall i, (0 <= i < 10)%Z -> live A7 (Z_to_bv 64 (pixes i)) = None /\ live A7 (Z_to_bv 64 (datad i)) = None) ->
  ~ pd_gone pa parr ba barr pixes datad q.
Proof.
  intros A7 pa parr ba barr pixes datad q k Lq N1 N2 N3 N4 NP [IN | (i & Hi & [E|E])].
  - unfold PA4 in IN. cbn [map In] in IN. destruct IN as [E|[E|[E|[E|[]]]]]; subst q; congruence.
  - destruct (NP i Hi) as [X _]. subst q. congruence.
  - destruct (NP i Hi) as [_ X]. subst q. congruence.
Qed.

Lemma not_in_pa4 : forall (A7 : AS) pa parr ba barr (q : word) k,
  live A7 q = Some k -> live A7 (Z_to_bv 64 pa) = None -> live A7 (Z_to_bv 64 parr) = None ->
  live A7 (Z_to_bv 64 ba) = None -> live A7 (Z_to_bv 64 barr) = None -> ~ In q (PA4 pa parr ba barr).
Proof.
  intros A7 pa parr ba barr q k Lq N1 N2 N3 N4 IN.
  unfold PA4 in IN. cbn [map In] in IN. destruct IN as [E|[E|[E|[E|[]]]]]; subst q; congruence.
Qed.

Lemma bd_pdmem : forall C Ar A Ak m M1 mk md (s bil pixs parr w h i pix data : Z) v,
  Cok C -> W C A m md -> live A (Z_to_bv 64 pixs) = Some 64%Z -> (0 <= pixs < 2 ^ 64)%Z -> live Ar (Z_to_bv 64 pixs) = Some 64%Z ->
  bd_keep C A Ak m M1 mk s bil pixs v ->
  live Ak (Z_to_bv 64 parr) = Some 80%Z -> (0 <= parr < 2 ^ 64)%Z -> Z_to_bv 64 parr <> Z_to_bv 64 bil -> Z_to_bv 64 parr <> Z_to_bv 64 pixs ->
  (0 <= i < 10)%Z -> Z_to_bv 64 pix <> Z_to_bv 64 bil ->
  live Ak (Z_to_bv 64 pix) = Some 64%Z -> live Ak (Z_to_bv 64 data) = Some (4 * (wpl_of w 8 * h))%Z ->
  bc_mem C Ar A m parr w h i pix data -> pd_mem C (c_A0 C) Ak mk parr w h i pix data.
Proof.
  intros C Ar A Ak m M1 mk md s bil pixs parr w h i pix data v CK HW Lp Gp Lrp BK Lpa Gpa NEpb NEpp Hi NEb Lk Ldk BM.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as HLS.
  destruct BM as (G1 & G2 & G3 & G4 & NE & NRp & NRd & N0p & N0d & Lx & Ld & PX & Rp).
  pose proof BK as (_ & _ & KEEP & _).
  assert (NEz : pix <> pixs) by (intros E; subst pix; rewrite NRp in Lrp; discriminate Lrp).
  pose proof (exW_blk_apart C A m md pix pixs 64 64 CK HW Lx Lp NEz ltac:(lia) Gp ltac:(lia) ltac:(lia)) as AP.
  refine (conj G1 (conj G2 (conj G3 (conj G4 (conj NE (conj N0p (conj N0d (conj N0p (conj N0d (conj Lk (conj Ldk (conj _ _)))))))))))).
  - apply (PIXat_frame m mk pix _ PX). intros x Hx.
    apply (KEEP (Z_to_bv 64 pix) 64%Z x Lk NEb); rewrite ?u_Z2bv by lia; lia.
  - rewrite (bd_keep_rdn C A Ak m M1 mk md s bil pixs v (Z_to_bv 64 parr) 80 (parr + 8 * i) 8 CK HW Lp Gp BK Lpa NEpb NEpp)
      by (rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    exact Rp.
Qed.

Lemma bdt_cs_110 : forall r, AllocIface.callee_saved r -> ~ In r [1; 10]%bv.
Proof.
  intros r Hr.
  destruct (cs_cases r Hr) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]; subst r; notin_lit.
Qed.
Lemma bdt_none : forall (A A' : AS) (q : word), sub_live A A' -> live A' q = None -> live A q = None.
Proof. intros A A' q S H. destruct (live A q) eqn:E; [apply S in E; congruence | reflexivity]. Qed.
Lemma bdt_sub1 : forall (A A' : AS) (p : word), live A' p = None -> (forall q, q <> p -> live A' q = live A q) -> sub_live A' A.
Proof.
  intros A A' p Hn Heq q k Hq. destruct (bv_eq_dec _ q p) as [->|NE]; [rewrite Hn in Hq; discriminate Hq|].
  rewrite <- (Heq q NE). exact Hq.
Qed.

Lemma bd_free1 : forall C A m M1 md Ak mk vmk rk (s bil pixs X n E R : Z) (v : pixv) (S : TSet) (P : machine_state -> Prop),
  Cok C -> W C Ak mk (with_vmmaps vmk md) ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 2048 <= s)%Z -> (s <= c_top C)%Z -> (0 <= pixs)%Z -> (pixs + 64 < 2 ^ 64)%Z ->
  bd_keep C A Ak m M1 mk s bil pixs v ->
  getr rk 2 = Z_to_bv 64 (s - 48) -> getr rk 4 = Z_to_bv 64 0x56270 ->
  live Ak (Z_to_bv 64 X) = Some n -> live (c_A0 C) (Z_to_bv 64 X) = None -> Z_to_bv 64 X <> Z_to_bv 64 pixs ->
  ret_ok (Z_to_bv 64 R) ->
  reach SEGS (mkst rk (Z_to_bv 64 E) mk al_rom) P ->
  (forall fin, P fin -> exists r1, fin = mkst r1 (Z_to_bv 64 0x3c230) mk al_rom /\ getr r1 1 = Z_to_bv 64 R /\
                               getr r1 10 = Z_to_bv 64 X /\ regs_agree (fun r => In r [1; 10]%list) rk r1) ->
  (forall A' m' vm' r', W C A' m' (with_vmmaps vm' md) -> cs_kept rk r' -> bd_keep C A A' m M1 m' s bil pixs v ->
     POSTM C A' (s - 48) mk m' -> live A' (Z_to_bv 64 X) = None -> (forall q, q <> Z_to_bv 64 X -> live A' q = live Ak q) ->
     sub_live A' Ak -> roomtr Ak vmk A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 R) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst rk (Z_to_bv 64 E) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m M1 md Ak mk vmk rk s bil pixs X n E R v S P CK HW Hs16 Hlo Htop Gp0 Gp64 BK R2 R4 LX L0X NXp Hret SEG SP K.
  pose proof LSTK_val as HLS.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | exact SEG |].
  intros fin Pf. destruct (SP fin Pf) as (r1 & -> & Q1 & Q10 & AG).
  refine (W_free16 C Ak mk (with_vmmaps vmk md) r1 (Z_to_bv 64 X) (Z_to_bv 64 R) n (s - 48) S CK HW Q10 LX L0X Q1 Hret _ _ _ _ _ _).
  - rewrite (AG 4%bv ltac:(notin_lit)). exact R4.
  - rewrite (AG 2%bv ltac:(notin_lit)). exact R2.
  - rewrite <- Zminus_mod_idemp_l, Hs16. reflexivity.
  - unfold ALLOC_STACK. lia.
  - lia.
  - intros A' m' vm' r' HW' CS LXn LEQ PM RT.
    rewrite with_vmmaps_twice in HW' |- *. rewrite with_vmmaps_vmmaps in RT.
    assert (SUB : sub_live A' Ak) by exact (bdt_sub1 Ak A' _ LXn LEQ).
    pose proof BK as (_ & LpK & _).
    assert (Lp' : live A' (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ _ (not_eq_sym NXp)); exact LpK).
    apply (K A' m' vm' r' HW'); try assumption.
    + intros r Hr. rewrite (CS r Hr). exact (AG r (bdt_cs_110 r Hr)).
    + exact (bd_keep_postm C A Ak A' m M1 mk m' (with_vmmaps vm' md) s bil pixs v CK HW' ltac:(lia) ltac:(lia) Gp0 Gp64 BK PM SUB Lp').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem bilateralDestroy_W : bilateralDestroy_contract.
Proof.
  intros C Ar A m md regs s pp bil pixs w h datas b ret S CK HW H2 Hs16 Hlo Hspp Hpp ALpp H1 Hret H4 H10 Rpp BO Hw Hh Lpx L0px Lrpx HK.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as HLS. unfold BD_WIN in Hlo.
  destruct BO as (CE & Bbil & Bnc & Bkx & Bkf & Bsp & Brg & Hmin & Hmax & NCV & KX & KF & PXs & PXb & Bbsc & Bdat & PCs & PBk
                  & Npa & Npar & Nba & Nbar & BM & Gls & NAls & N0ls & Lls & LFk & CH).
  destruct Bbil as (Gb1 & Gb2 & Gb3 & Lbil & NRbil & N0bil).
  destruct Bbsc as (Gc1 & Gc2 & Gc3 & Lbsc & NRbsc & N0bsc).
  destruct Bdat as (Gd1 & Gd2 & Gd3 & Ldat & NRdat & N0dat).
  cbn [p_w p_h hdv V2LeptPixCopyTR.hdv] in Gd2, Ldat.
  assert (WPb : (1 <= wpl_of (w + 22) 8)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia).
  assert (SZd : (0 <= 4 * (wpl_of (w + 22) 8 * (h + 22)))%Z) by nia.
  destruct CH as (A1 & A7 & Ac3 & S17 & S73 & S3f & L1bsc & L1dat & NEbd & Cbil & Cnc & Ckx & Ckf & Csp & Crg & NEk
                  & N7pa & N7par & N7ba & N7bar & PB3 & NEpb & PX7 & DST & N3ls & N3lf & DSTl & NIN).
  assert (FLD : forall c, In c (bc_bl2 pixs (bw_bsc b) (bw_minv b) (bw_maxv b) (bw_nc b) (bw_kx b) (bw_kf b) (bw_spat b) (bw_rng b)
                                ++ [(88%Z, 8%nat, bw_pa b); (96%Z, 8%nat, bw_ls b)]) ->
      rdn SEGS m (Z_to_bv 64 (bil + c_off c)) (c_len c) = Some (Z_to_le_bytes (c_len c) (c_val c)))
    by (apply Forall_forall; exact CE).
  bd_fld FLD (0%Z, 8%nat, pixs) R0. rewrite Z.add_0_r in R0.
  bd_fld FLD (8%Z, 8%nat, bw_bsc b) R8.
  pose proof PXs as (Gp0 & Gp64 & _).
  destruct (exW_blk_rng C A m md pixs 64 CK HW Lpx ltac:(lia) ltac:(lia)) as (Bp1 & Bp2 & Bp3).
  assert (NEbpz : bil <> pixs) by (intros E; rewrite E in NRbil; rewrite NRbil in Lrpx; discriminate Lrpx).
  pose proof (exW_blk_apart C A m md bil pixs 104 64 CK HW Lbil Lpx NEbpz ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as APbp.
  assert (NEbp : Z_to_bv 64 bil <> Z_to_bv 64 pixs) by (apply zneq_w; lia).
  destruct (bl_A al_rom fx regs m s pp bil ltac:(lia) Hspp ltac:(lia) Gb1 ltac:(lia) ALpp (al16_mod8 _ Gb3) Rpp
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H10)
    as (fin1 & RUN1 & r1 & M1 & -> & RI1 & S8 & S16 & S24 & S32 & S40 & Q1 & Q2 & Q8 & Q9 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  destruct (rinv_WP2 C (c_A0 C) A m md M1 [((s - 40)%Z, 40%Z)] s CK HW (W_sub0 _ _ _ _ HW) ltac:(lia) RI1
              ltac:(constructor; [left; cbn [fst snd]; lia | constructor])) as [HW1 PM1].
  assert (SLb : slotok C A (s - 48) bil (Some (Z_to_bv 64 bil, 104%Z)))
    by (cbn [slotok]; rewrite u_Z2bv by lia; refine (conj Lbil (conj N0bil _)); lia).
  assert (R0m : rdn SEGS M1 (Z_to_bv 64 bil) 8 = Some (Z_to_le_bytes 8 pixs)).
  { rewrite (rinv_rdn SEGS _ m M1 bil 8 RI1); [exact R0 | lia | cbn; lia |].
    intros r Hr. destruct Hr as [<-|[]]. cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (PXs1 : PIXat M1 pixs (set_rc (hdv w h 8 0 datas) 2)).
  { apply (PIXat_frame m M1 pixs _ PXs). intros x Hx. apply (proj2 RI1). intros r Hr. destruct Hr as [<-|[]]. unfold inreg. cbn [fst snd]. lia. }
  replace (Z_to_bv 64 104492) with (0x1982c : word) by (apply bv_eq; reflexivity).
  apply (pixDestroy_dec_W C A M1 md r1 (s - 48) bil pixs (set_rc (hdv w h 8 0 datas) 2) (Some (Z_to_bv 64 bil, 104%Z)) (Z_to_bv 64 240280) S
           CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           (al16_mod8 _ Gb3) Q10 SLb R0m PXs1 eq_refl Lpx L0px).
  { intros p k E. injection E as <- <-. exact NEbp. }
  intros m2 r2 HW2 CS2 PX2 R0z K2 MG2.
  destruct (bd_init C A m md M1 m2 s bil pixs (hdv w h 8 0 datas) CK HW ltac:(lia) ltac:(lia) Lbil Lpx ltac:(lia) ltac:(lia) ltac:(lia)
              RI1 (proj1 PM1) K2 PX2) as [BK2 BT8].
  assert (BT2 : bd_thru m2 m bil) by (intros a nn Ha Hb; apply BT8; lia).
  assert (V2a : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (V9a : getr r2 9 = Z_to_bv 64 bil) by (csr; reflexivity).
  destruct (bl_B al_rom fx r2 m2 s bil ltac:(lia) Gb1 ltac:(lia) V2a V9a)
    as (fin2 & RUN2 & r3 & M3 & -> & -> & P1 & P2 & P9 & P10 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN2 |].
  assert (P4 : getr r3 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  destruct Cbil as (Hc1 & Hc2 & Hc3 & L7bil & N1bil & _).
  assert (NEcbz : bw_bsc b <> bil) by (intros E; rewrite E in L1bsc; rewrite L1bsc in N1bil; discriminate N1bil).
  assert (NEdbz : bw_datas b <> bil) by (intros E; rewrite E in L1dat; rewrite L1dat in N1bil; discriminate N1bil).
  assert (NEcpz : bw_bsc b <> pixs) by (intros E; rewrite E in NRbsc; rewrite NRbsc in Lrpx; discriminate Lrpx).
  assert (NEdpz : bw_datas b <> pixs) by (intros E; rewrite E in NRdat; rewrite NRdat in Lrpx; discriminate Lrpx).
  assert (NEcb : Z_to_bv 64 (bw_bsc b) <> Z_to_bv 64 bil) by (apply zneq_w; lia).
  assert (NEdb : Z_to_bv 64 (bw_datas b) <> Z_to_bv 64 bil) by (apply zneq_w; lia).
  assert (NEpc : Z_to_bv 64 pixs <> Z_to_bv 64 (bw_bsc b)) by (apply zneq_w; lia).
  assert (NEpd : Z_to_bv 64 pixs <> Z_to_bv 64 (bw_datas b)) by (apply zneq_w; lia).
  pose proof (exW_blk_apart C A m md (bw_bsc b) pixs 64 64 CK HW Lbsc Lpx NEcpz ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as APcp.
  pose proof BK2 as (_ & _ & KEEP2 & _).
  assert (R8m : rdn SEGS m2 (Z_to_bv 64 (bil + 8)) 8 = Some (Z_to_le_bytes 8 (bw_bsc b)))
    by (rewrite BT8 by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact R8).
  assert (PXb2 : PIXat m2 (bw_bsc b) (hdv (w + 22) (h + 22) 8 0 (bw_datas b))).
  { apply (PIXat_frame m m2 _ _ PXb). intros x Hx.
    apply (KEEP2 (Z_to_bv 64 (bw_bsc b)) 64%Z x Lbsc NEcb); rewrite ?u_Z2bv by lia; lia. }
  assert (SL8 : slotok C A (s - 48) (bil + 8) (Some (Z_to_bv 64 bil, 104%Z)))
    by (cbn [slotok]; rewrite u_Z2bv by lia; refine (conj Lbil (conj N0bil _)); lia).
  replace (Z_to_bv 64 104492) with (0x1982c : word) by (apply bv_eq; reflexivity).
  apply (pixDestroy_free_W C A m2 md r3 (s - 48) (bil + 8) (bw_bsc b) (4 * (wpl_of (w + 22) 8 * (h + 22)))%Z
           (hdv (w + 22) (h + 22) 8 0 (bw_datas b)) (Some (Z_to_bv 64 bil, 104%Z)) (Z_to_bv 64 240288) S
           CK HW2 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) P1
           ltac:(red; apply bv_eq; reflexivity) P4 (al16_plus_mod8 bil 8 Gb3 eq_refl) P10 SL8 R8m PXb2 eq_refl eq_refl eq_refl
           Lbsc N0bsc Ldat N0dat ltac:(nia) (not_eq_sym NEbd)).
  { intros p k E. injection E as <- <-. exact (conj (not_eq_sym NEcb) (not_eq_sym NEdb)). }
  intros A3 m3 vm3 r4 HW3 CS3 Lbsc3 Ldat3 LEQ3 SUB3 PD3 R8z RT3.
  assert (Lbil3 : live A3 (Z_to_bv 64 bil) = Some 104%Z) by (rewrite (LEQ3 _ (not_eq_sym NEcb) (not_eq_sym NEdb)); exact Lbil).
  assert (Lpx3 : live A3 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ3 _ NEpc NEpd); exact Lpx).
  pose proof (bd_keep_postd C A A A3 m M1 m2 m3 (with_vmmaps vm3 md) s (bil + 8) bil pixs (hdv w h 8 0 datas) CK HW3
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Lbil3 (not_eq_sym NEbp) BK2 PD3 SUB3 Lpx3) as BK3.
  pose proof (bd_thru_postd C A3 m2 m m3 s (bil + 8) bil BT2 PD3 Lbil3 Gb1 ltac:(lia) (or_introl eq_refl)) as BT3.
  assert (W2b : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (W9b : getr r4 9 = Z_to_bv 64 bil) by (csr; reflexivity).
  destruct (bl_C al_rom fx r4 m3 s bil ltac:(lia) Gb1 ltac:(lia) W2b W9b)
    as (fin3 & RUN3 & r5 & M5 & -> & -> & U1 & U2 & U9 & U10 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN3 |].
  assert (U4 : getr r5 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  destruct PBk as (Gpa & Gpar & Gba & Gbar & Lpa & Lpar & Lba & Lbar & N0pa & N0par & N0ba & N0bar).
  bd_fld FLD (88%Z, 8%nat, bw_pa b) R88.
  pose proof (S17 _ _ L1bsc) as L7bsc. pose proof (S17 _ _ L1dat) as L7dat.
  assert (La3 : live A3 (Z_to_bv 64 (bw_pa b)) = Some 32%Z)
    by (rewrite (LEQ3 _ (live_neq' _ _ _ _ L7bsc N7pa) (live_neq' _ _ _ _ L7dat N7pa)); exact Lpa).
  assert (Lpar3 : live A3 (Z_to_bv 64 (bw_parr b)) = Some 80%Z)
    by (rewrite (LEQ3 _ (live_neq' _ _ _ _ L7bsc N7par) (live_neq' _ _ _ _ L7dat N7par)); exact Lpar).
  assert (Lba3 : live A3 (Z_to_bv 64 (bw_ba b)) = Some 24%Z)
    by (rewrite (LEQ3 _ (live_neq' _ _ _ _ L7bsc N7ba) (live_neq' _ _ _ _ L7dat N7ba)); exact Lba).
  assert (Lbar3 : live A3 (Z_to_bv 64 (bw_barr b)) = Some 80%Z)
    by (rewrite (LEQ3 _ (live_neq' _ _ _ _ L7bsc N7bar) (live_neq' _ _ _ _ L7dat N7bar)); exact Lbar).
  assert (PC3 : pixa_cells m3 (bw_pa b) (bw_parr b) (bw_ba b) (bw_barr b) 10).
  { apply (pixa_cells_keep m m3 _ _ _ _ 10 PCs).
    - intros a nn Ha Hb.
      apply (bd_keep_rdn C A A3 m M1 m3 md s bil pixs (hdv w h 8 0 datas) (Z_to_bv 64 (bw_pa b)) 32 a nn CK HW Lpx ltac:(lia) BK3 La3
               (live_neq' _ _ _ _ L7bil N7pa) (live_neq' _ _ _ _ Lrpx Npa)); rewrite u_Z2bv by lia; lia.
    - intros a nn Ha Hb.
      apply (bd_keep_rdn C A A3 m M1 m3 md s bil pixs (hdv w h 8 0 datas) (Z_to_bv 64 (bw_ba b)) 24 a nn CK HW Lpx ltac:(lia) BK3 Lba3
               (live_neq' _ _ _ _ L7bil N7ba) (live_neq' _ _ _ _ Lrpx Nba)); rewrite u_Z2bv by lia; lia. }
  assert (PDS : pd_static C (c_A0 C) (Z_to_bv 64 bil) (bw_pa b) (bw_parr b) (bw_ba b) (bw_barr b) w h (bw_pixes b) (bw_datad b)).
  { refine (conj Gpa (conj Gpar (conj Gba (conj Gbar (conj N0pa (conj N0par (conj N0ba (conj N0bar (conj N0pa (conj N0par (conj N0ba
              (conj N0bar (conj N0bil (conj N0bil (conj NEpb (conj Hw (conj Hh (conj DST (conj NIN (conj _ _)))))))))))))))))))).
    - intros j Hj. destruct (PX7 j Hj) as (X1 & X2 & _). exact (conj (live_neq _ _ _ _ L7bil X1) (live_neq _ _ _ _ L7bil X2)).
    - exact (not_in_pa4 A7 _ _ _ _ _ _ L7bil N7pa N7par N7ba N7bar). }
  assert (PDM : forall j, (0 <= j < 10)%Z -> pd_mem C (c_A0 C) A3 m3 (bw_parr b) w h j (bw_pixes b j) (bw_datad b j)).
  { intros j Hj. destruct (PX7 j Hj) as (X1 & X2 & _). pose proof (BM j Hj) as BMj.
    destruct BMj as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Lxj & Ldj & _).
    apply (bd_pdmem C Ar A A3 m M1 m3 md s bil pixs (bw_parr b) w h j (bw_pixes b j) (bw_datad b j) (hdv w h 8 0 datas) CK HW Lpx ltac:(lia) Lrpx BK3
             Lpar3 Gpar (live_neq' _ _ _ _ L7bil N7par) (live_neq' _ _ _ _ Lrpx Npar) Hj (live_neq' _ _ _ _ L7bil X1)).
    - rewrite (LEQ3 _ (live_neq' _ _ _ _ L7bsc X1) (live_neq' _ _ _ _ L7dat X1)). exact Lxj.
    - rewrite (LEQ3 _ (live_neq' _ _ _ _ L7bsc X2) (live_neq' _ _ _ _ L7dat X2)). exact Ldj.
    - exact (BM j Hj). }
  assert (SL88 : slotok C A3 (s - 48) (bil + 88) (Some (Z_to_bv 64 bil, 104%Z)))
    by (cbn [slotok]; rewrite u_Z2bv by lia; refine (conj Lbil3 (conj N0bil _)); lia).
  assert (R88m : rdn SEGS m3 (Z_to_bv 64 (bil + 88)) 8 = Some (Z_to_le_bytes 8 (bw_pa b))).
  { rewrite (POSTD_rdn_blk C A3 (s - 48) (bil + 8) m2 m3 (Z_to_bv 64 bil) 104 (bil + 88) 8 PD3 Lbil3)
      by (rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    rewrite BT8 by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R88. }
  apply (pixaDestroy10_W C (c_A0 C) A3 m3 (with_vmmaps vm3 md) r5 (s - 48) (bil + 88) 104 (bw_pa b) (bw_parr b) (bw_ba b) (bw_barr b) w h
           (Z_to_bv 64 bil) (bw_pixes b) (bw_datad b) (Z_to_bv 64 240296) S
           CK HW3 U2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold PAD_WIN, ALLOC_STACK; lia) ltac:(lia) U1
           ltac:(red; apply bv_eq; reflexivity) U4 (al16_plus_mod8 bil 88 Gb3 eq_refl) U10 SL88 R88m (W_sub0 _ _ _ _ HW3) PC3 La3 Lpar3 Lba3 Lbar3 PDS PDM).
  intros A4 m4 vm4 r6 HW4 CS4 GONE4 LEQ4 SUB04 PD4 R88z RT4.
  assert (SUB4 : sub_live A4 A3).
  { intros q k Hq. destruct (pd_gone_dec (bw_pa b) (bw_parr b) (bw_ba b) (bw_barr b) (bw_pixes b) (bw_datad b) q) as [G|G].
    - rewrite (GONE4 q G) in Hq. discriminate Hq.
    - rewrite <- (LEQ4 q G). exact Hq. }
  assert (NG7 : forall q k, live A7 q = Some k -> ~ pd_gone (bw_pa b) (bw_parr b) (bw_ba b) (bw_barr b) (bw_pixes b) (bw_datad b) q).
  { intros q k Lq. apply (not_gone_7 A7 _ _ _ _ _ _ q k Lq N7pa N7par N7ba N7bar).
    intros i Hi. destruct (PX7 i Hi) as (X1 & X2 & _). exact (conj X1 X2). }
  assert (NGp : ~ pd_gone (bw_pa b) (bw_parr b) (bw_ba b) (bw_barr b) (bw_pixes b) (bw_datad b) (Z_to_bv 64 pixs)).
  { apply (not_gone_7 Ar _ _ _ _ _ _ _ _ Lrpx Npa Npar Nba Nbar).
    intros i Hi. destruct (BM i Hi) as (_ & _ & _ & _ & _ & X1 & X2 & _). exact (conj X1 X2). }
  assert (Lbil4 : live A4 (Z_to_bv 64 bil) = Some 104%Z) by (rewrite (LEQ4 _ (NG7 _ _ L7bil)); exact Lbil3).
  assert (Lpx4 : live A4 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ4 _ NGp); exact Lpx3).
  pose proof (bd_keep_postd C A A3 A4 m M1 m3 m4 (with_vmmaps vm4 (with_vmmaps vm3 md)) s (bil + 88) bil pixs (hdv w h 8 0 datas) CK HW4
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Lbil4 (not_eq_sym NEbp) BK3 PD4 SUB4 Lpx4) as BK4.
  pose proof (bd_thru_postd C A4 m3 m m4 s (bil + 88) bil BT3 PD4 Lbil4 Gb1 ltac:(lia) (or_intror eq_refl)) as BT4.
  rewrite with_vmmaps_vmmaps in RT4.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT3 RT4 ltac:(lia) ltac:(lia)) as RT4'.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (Hs' : (4096 + 48 <= s <= 2 ^ 47)%Z) by lia.
  assert (Hb' : (bil + 104 <= s - 48)%Z) by lia.
  destruct Bsp as (Gs1 & Gs2 & Gs3 & Lsp & NRsp & N0sp).
  destruct Brg as (Gr1 & Gr2 & Gr3 & Lrg & NRrg & N0rg).
  destruct Bnc as (Gn1 & Gn2 & Gn3 & Lnc & NRnc & N0nc).
  destruct Bkx as (Gx1 & Gx2 & Gx3 & Lkx & NRkx & N0kx).
  destruct Bkf as (Gf1 & Gf2 & Gf3 & Lkf & NRkf & N0kf).
  destruct Csp as (_ & _ & _ & L7sp & N1sp & _).
  destruct Crg as (_ & _ & _ & L7rg & N1rg & _).
  destruct Cnc as (_ & _ & _ & L7nc & N1nc & _).
  destruct Ckx as (_ & _ & _ & L7kx & N1kx & _).
  destruct Ckf as (_ & _ & _ & L7kf & N1kf & _).
  destruct NEk as (NEk1 & NEk2 & NEk3).
  assert (A4of : forall q k, live A7 q = Some k -> live A1 q = None -> live A4 q = live A q).
  { intros q k L7q N1q. rewrite (LEQ4 _ (NG7 _ _ L7q)). apply LEQ3; [exact (live_neq' _ _ _ _ L1bsc N1q) | exact (live_neq' _ _ _ _ L1dat N1q)]. }
  assert (RT4z : roomtr A (m_vmmaps md) A4 vm4 0 0) by exact RT4'.
  assert (NEbila : Z_to_bv 64 bil <> Z_to_bv 64 (bw_spat b)) by exact (live_neq_sz _ _ _ _ _ Lbil Lsp ltac:(lia)).
  assert (Lap : live A4 (Z_to_bv 64 (bw_spat b)) = Some 44%Z) by (rewrite (A4of _ _ L7sp N1sp); exact Lsp).
  bd_fld FLD (32%Z, 8%nat, bw_spat b) Ra.
  assert (Ram : rdn SEGS m4 (Z_to_bv 64 (bil + 32)) 8 = Some (Z_to_le_bytes 8 (bw_spat b))) by (rewrite BT4 by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Ra).
  assert (Z2a : getr r6 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (Z9a : getr r6 9 = Z_to_bv 64 bil) by (csr; reflexivity).
  assert (Z4a : getr r6 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  apply (bd_free1 C A m M1 md A4 m4 vm4 r6 s bil pixs (bw_spat b) 44 240296 240304 (hdv w h 8 0 datas) S _ CK HW4 Hs16 ltac:(lia) ltac:(lia) Gp0 Gp64 BK4 Z2a Z4a Lap N0sp (live_neq' _ _ _ _ Lrpx NRsp) ltac:(red; apply bv_eq; reflexivity) (bl_F0 al_rom fx r6 m4 s bil (bw_spat b) Hs' Gb1 Hb' ltac:(lia) Ram Z2a Z9a)).
  { intros fin (r1' & M' & -> & -> & Q1' & _ & _ & Q10' & AG'). exists r1'. auto. }
  intros Aa ma vma ra HWa CSa BKa PMa Lax LEQa SUBa RTa.
  assert (Lbila : live Aa (Z_to_bv 64 bil) = Some 104%Z) by (rewrite (LEQa _ NEbila); exact Lbil4).
  pose proof (bd_thru_postm C Aa m4 m ma s bil BT4 PMa Lbila Gb1 ltac:(lia)) as BTa.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT4z RTa ltac:(lia) ltac:(lia)) as RTaz. cbn [Z.add] in RTaz.
  assert (DFba : Z_to_bv 64 (bw_rng b) <> Z_to_bv 64 (bw_spat b)) by (exact (live_neq_sz _ _ _ _ _ Lrg Lsp ltac:(lia))).
  assert (NEbilb : Z_to_bv 64 bil <> Z_to_bv 64 (bw_rng b)) by exact (live_neq_sz _ _ _ _ _ Lbil Lrg ltac:(lia)).
  assert (Lbp : live Aa (Z_to_bv 64 (bw_rng b)) = Some 1024%Z) by (rewrite (LEQa _ DFba); rewrite (A4of _ _ L7rg N1rg); exact Lrg).
  bd_fld FLD (40%Z, 8%nat, bw_rng b) Rb.
  assert (Rbm : rdn SEGS ma (Z_to_bv 64 (bil + 40)) 8 = Some (Z_to_le_bytes 8 (bw_rng b))) by (rewrite BTa by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Rb).
  assert (Z2b : getr ra 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (Z9b : getr ra 9 = Z_to_bv 64 bil) by (csr; reflexivity).
  assert (Z4b : getr ra 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  apply (bd_free1 C A m M1 md Aa ma vma ra s bil pixs (bw_rng b) 1024 240304 240312 (hdv w h 8 0 datas) S _ CK HWa Hs16 ltac:(lia) ltac:(lia) Gp0 Gp64 BKa Z2b Z4b Lbp N0rg (live_neq' _ _ _ _ Lrpx NRrg) ltac:(red; apply bv_eq; reflexivity) (bl_F1 al_rom fx ra ma s bil (bw_rng b) Hs' Gb1 Hb' ltac:(lia) Rbm Z2b Z9b)).
  { intros fin (r1' & M' & -> & -> & Q1' & _ & _ & Q10' & AG'). exists r1'. auto. }
  intros Ab mb vmb rb HWb CSb BKb PMb Lbx LEQb SUBb RTb.
  assert (Lbilb : live Ab (Z_to_bv 64 bil) = Some 104%Z) by (rewrite (LEQb _ NEbilb); exact Lbila).
  pose proof (bd_thru_postm C Ab ma m mb s bil BTa PMb Lbilb Gb1 ltac:(lia)) as BTb.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RTaz RTb ltac:(lia) ltac:(lia)) as RTbz. cbn [Z.add] in RTbz.
  assert (DFca : Z_to_bv 64 (bw_nc b) <> Z_to_bv 64 (bw_spat b)) by (exact (live_neq_sz _ _ _ _ _ Lnc Lsp ltac:(lia))).
  assert (DFcb : Z_to_bv 64 (bw_nc b) <> Z_to_bv 64 (bw_rng b)) by (exact (live_neq_sz _ _ _ _ _ Lnc Lrg ltac:(lia))).
  assert (NEbilc : Z_to_bv 64 bil <> Z_to_bv 64 (bw_nc b)) by exact (live_neq_sz _ _ _ _ _ Lbil Lnc ltac:(lia)).
  assert (Lcp : live Ab (Z_to_bv 64 (bw_nc b)) = Some 40%Z) by (rewrite (LEQb _ DFcb); rewrite (LEQa _ DFca); rewrite (A4of _ _ L7nc N1nc); exact Lnc).
  bd_fld FLD (64%Z, 8%nat, bw_nc b) Rc.
  assert (Rcm : rdn SEGS mb (Z_to_bv 64 (bil + 64)) 8 = Some (Z_to_le_bytes 8 (bw_nc b))) by (rewrite BTb by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Rc).
  assert (Z2c : getr rb 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (Z9c : getr rb 9 = Z_to_bv 64 bil) by (csr; reflexivity).
  assert (Z4c : getr rb 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  apply (bd_free1 C A m M1 md Ab mb vmb rb s bil pixs (bw_nc b) 40 240312 240320 (hdv w h 8 0 datas) S _ CK HWb Hs16 ltac:(lia) ltac:(lia) Gp0 Gp64 BKb Z2c Z4c Lcp N0nc (live_neq' _ _ _ _ Lrpx NRnc) ltac:(red; apply bv_eq; reflexivity) (bl_F2 al_rom fx rb mb s bil (bw_nc b) Hs' Gb1 Hb' ltac:(lia) Rcm Z2c Z9c)).
  { intros fin (r1' & M' & -> & -> & Q1' & _ & _ & Q10' & AG'). exists r1'. auto. }
  intros Ac mc vmc rc HWc CSc BKc PMc Lcx LEQc SUBc RTc.
  assert (Lbilc : live Ac (Z_to_bv 64 bil) = Some 104%Z) by (rewrite (LEQc _ NEbilc); exact Lbilb).
  pose proof (bd_thru_postm C Ac mb m mc s bil BTb PMc Lbilc Gb1 ltac:(lia)) as BTc.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RTbz RTc ltac:(lia) ltac:(lia)) as RTcz. cbn [Z.add] in RTcz.
  assert (DFea : Z_to_bv 64 (bw_kx b) <> Z_to_bv 64 (bw_spat b)) by (exact (live_neq_sz _ _ _ _ _ Lkx Lsp ltac:(lia))).
  assert (DFeb : Z_to_bv 64 (bw_kx b) <> Z_to_bv 64 (bw_rng b)) by (apply zneq_w; [lia | lia | lia]).
  assert (DFec : Z_to_bv 64 (bw_kx b) <> Z_to_bv 64 (bw_nc b)) by (exact (live_neq_sz _ _ _ _ _ Lkx Lnc ltac:(lia))).
  assert (NEbile : Z_to_bv 64 bil <> Z_to_bv 64 (bw_kx b)) by exact (live_neq_sz _ _ _ _ _ Lbil Lkx ltac:(lia)).
  assert (Lep : live Ac (Z_to_bv 64 (bw_kx b)) = Some 1024%Z) by (rewrite (LEQc _ DFec); rewrite (LEQb _ DFeb); rewrite (LEQa _ DFea); rewrite (A4of _ _ L7kx N1kx); exact Lkx).
  bd_fld FLD (72%Z, 8%nat, bw_kx b) Re.
  assert (Rem : rdn SEGS mc (Z_to_bv 64 (bil + 72)) 8 = Some (Z_to_le_bytes 8 (bw_kx b))) by (rewrite BTc by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Re).
  assert (Z2e : getr rc 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (Z9e : getr rc 9 = Z_to_bv 64 bil) by (csr; reflexivity).
  assert (Z4e : getr rc 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  apply (bd_free1 C A m M1 md Ac mc vmc rc s bil pixs (bw_kx b) 1024 240320 240328 (hdv w h 8 0 datas) S _ CK HWc Hs16 ltac:(lia) ltac:(lia) Gp0 Gp64 BKc Z2e Z4e Lep N0kx (live_neq' _ _ _ _ Lrpx NRkx) ltac:(red; apply bv_eq; reflexivity) (bl_F3 al_rom fx rc mc s bil (bw_kx b) Hs' Gb1 Hb' ltac:(lia) Rem Z2e Z9e)).
  { intros fin (r1' & M' & -> & -> & Q1' & _ & _ & Q10' & AG'). exists r1'. auto. }
  intros Ae me vme re HWe CSe BKe PMe Lex LEQe SUBe RTe.
  assert (Lbile : live Ae (Z_to_bv 64 bil) = Some 104%Z) by (rewrite (LEQe _ NEbile); exact Lbilc).
  pose proof (bd_thru_postm C Ae mc m me s bil BTc PMe Lbile Gb1 ltac:(lia)) as BTe.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RTcz RTe ltac:(lia) ltac:(lia)) as RTez. cbn [Z.add] in RTez.
  assert (DFfa : Z_to_bv 64 (bw_kf b) <> Z_to_bv 64 (bw_spat b)) by (exact (live_neq_sz _ _ _ _ _ Lkf Lsp ltac:(lia))).
  assert (DFfb : Z_to_bv 64 (bw_kf b) <> Z_to_bv 64 (bw_rng b)) by (apply zneq_w; [lia | lia | lia]).
  assert (DFfc : Z_to_bv 64 (bw_kf b) <> Z_to_bv 64 (bw_nc b)) by (exact (live_neq_sz _ _ _ _ _ Lkf Lnc ltac:(lia))).
  assert (DFfe : Z_to_bv 64 (bw_kf b) <> Z_to_bv 64 (bw_kx b)) by (apply zneq_w; [lia | lia | lia]).
  assert (NEbilf : Z_to_bv 64 bil <> Z_to_bv 64 (bw_kf b)) by exact (live_neq_sz _ _ _ _ _ Lbil Lkf ltac:(lia)).
  assert (Lfp : live Ae (Z_to_bv 64 (bw_kf b)) = Some 1024%Z) by (rewrite (LEQe _ DFfe); rewrite (LEQc _ DFfc); rewrite (LEQb _ DFfb); rewrite (LEQa _ DFfa); rewrite (A4of _ _ L7kf N1kf); exact Lkf).
  bd_fld FLD (80%Z, 8%nat, bw_kf b) Rf.
  assert (Rfm : rdn SEGS me (Z_to_bv 64 (bil + 80)) 8 = Some (Z_to_le_bytes 8 (bw_kf b))) by (rewrite BTe by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Rf).
  assert (Z2f : getr re 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (Z9f : getr re 9 = Z_to_bv 64 bil) by (csr; reflexivity).
  assert (Z4f : getr re 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  apply (bd_free1 C A m M1 md Ae me vme re s bil pixs (bw_kf b) 1024 240328 240336 (hdv w h 8 0 datas) S _ CK HWe Hs16 ltac:(lia) ltac:(lia) Gp0 Gp64 BKe Z2f Z4f Lfp N0kf (live_neq' _ _ _ _ Lrpx NRkf) ltac:(red; apply bv_eq; reflexivity) (bl_F4 al_rom fx re me s bil (bw_kf b) Hs' Gb1 Hb' ltac:(lia) Rfm Z2f Z9f)).
  { intros fin (r1' & M' & -> & -> & Q1' & _ & _ & Q10' & AG'). exists r1'. auto. }
  intros Af mf vmf rf HWf CSf BKf PMf Lfx LEQf SUBf RTf.
  assert (Lbilf : live Af (Z_to_bv 64 bil) = Some 104%Z) by (rewrite (LEQf _ NEbilf); exact Lbile).
  pose proof (bd_thru_postm C Af me m mf s bil BTe PMf Lbilf Gb1 ltac:(lia)) as BTf.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RTez RTf ltac:(lia) ltac:(lia)) as RTfz. cbn [Z.add] in RTfz.
  assert (NG3 : forall q, live Ac3 q = None -> ~ pd_gone (bw_pa b) (bw_parr b) (bw_ba b) (bw_barr b) (bw_pixes b) (bw_datad b) q).
  { intros q Nq [IN | (i & Hi & [E|E])].
    - destruct PB3 as (_ & _ & _ & _ & PB1 & PB2 & PB3' & PB4 & _). unfold PA4 in IN. cbn [map In] in IN.
      destruct IN as [E|[E|[E|[E|[]]]]]; subst q; congruence.
    - destruct (PX7 i Hi) as (_ & _ & X & _). subst q. congruence.
    - destruct (PX7 i Hi) as (_ & _ & _ & X). subst q. congruence. }
  assert (OUT3 : forall q n, live Ac3 q = None -> live A q = Some n -> live Af q = Some n).
  { intros q n N3 LA.
    pose proof (S73 _ _ L7sp) as C1. pose proof (S73 _ _ L7rg) as C2. pose proof (S73 _ _ L7nc) as C3.
    pose proof (S73 _ _ L7kx) as C4. pose proof (S73 _ _ L7kf) as C5.
    pose proof (S73 _ _ (S17 _ _ L1bsc)) as C6. pose proof (S73 _ _ (S17 _ _ L1dat)) as C7.
    rewrite (LEQf _ (live_neq' _ _ _ _ C5 N3)), (LEQe _ (live_neq' _ _ _ _ C4 N3)), (LEQc _ (live_neq' _ _ _ _ C3 N3)),
            (LEQb _ (live_neq' _ _ _ _ C2 N3)), (LEQa _ (live_neq' _ _ _ _ C1 N3)), (LEQ4 _ (NG3 _ N3)).
    rewrite (LEQ3 _ (live_neq' _ _ _ _ C6 N3) (live_neq' _ _ _ _ C7 N3)). exact LA. }
  pose proof (S73 _ _ L7bil) as L3bil.
  assert (Llsf : live Af (Z_to_bv 64 (bw_ls b)) = Some 80%Z) by exact (OUT3 _ _ N3ls Lls).
  destruct (exW_blk_rng C Af mf (with_vmmaps vmf md) (bw_ls b) 80 CK HWf Llsf ltac:(lia) ltac:(lia)) as (Gl1 & Gl2 & Gl3).
  assert (NElsb : Z_to_bv 64 (bw_ls b) <> Z_to_bv 64 bil) by exact (live_neq' _ _ _ _ L3bil N3ls).
  assert (NElsp : Z_to_bv 64 (bw_ls b) <> Z_to_bv 64 pixs) by exact (live_neq' _ _ _ _ Lrpx NAls).
  pose proof BKf as (_ & Lpxf & _).
  assert (LFf : forall k, (0 <= k < 10)%Z -> live Af (Z_to_bv 64 (bw_linesf b k)) = Some (8 * h)%Z).
  { intros k Hk. destruct (LFk k Hk) as (_ & Lk & _). exact (OUT3 _ _ (N3lf k Hk) Lk). }
  assert (LFr : forall k, (0 <= k < 10)%Z -> (0 <= bw_linesf b k < 2 ^ 64)%Z /\ live (c_A0 C) (Z_to_bv 64 (bw_linesf b k)) = None /\
                  bw_linesf b k <> bil /\ bw_linesf b k <> bw_ls b /\
                  rdn SEGS mf (Z_to_bv 64 (bw_ls b + 8 * k)) 8 = Some (Z_to_le_bytes 8 (bw_linesf b k))).
  { intros k Hk. destruct (LFk k Hk) as (G0 & _ & _ & N0k & NEk & Rk & _).
    refine (conj G0 (conj N0k (conj _ (conj NEk _)))).
    - intros E. pose proof (N3lf k Hk) as X. rewrite E in X. congruence.
    - rewrite (bd_keep_rdn C A Af m M1 mf md s bil pixs (hdv w h 8 0 datas) (Z_to_bv 64 (bw_ls b)) 80 (bw_ls b + 8 * k) 8 CK HW Lpx ltac:(lia) BKf Llsf NElsb NElsp)
        by (rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      exact Rk. }
  bd_fld FLD (56%Z, 4%nat, 10%Z) R56.
  assert (R56m : rdn SEGS mf (Z_to_bv 64 (bil + 56)) 4 = Some (Z_to_le_bytes 4 10)) by (rewrite BTf by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact R56).
  bd_fld FLD (96%Z, 8%nat, bw_ls b) R96.
  assert (R96m : rdn SEGS mf (Z_to_bv 64 (bil + 96)) 8 = Some (Z_to_le_bytes 8 (bw_ls b))) by (rewrite BTf by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact R96).
  assert (Z2g : getr rf 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (Z9g : getr rf 9 = Z_to_bv 64 bil) by (csr; reflexivity).
  destruct (bl_G al_rom fx rf mf s bil Hs' Gb1 Hb' R56m Z2g Z9g) as (fing & RUNG & rg & Mg & -> & -> & G2 & G9 & G18 & G19 & AGg).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWf)) | exact (mp_lazy _ (w_pure _ _ _ _ HWf)) | exact RUNG |].
  apply (bld_loop_W 10 C Af Af mf mf (with_vmmaps vmf md) vmf rg rg s bil (bw_ls b) h 0 (bw_linesf b) S ltac:(reflexivity) ltac:(lia) CK HWf Hs16
           ltac:(unfold ALLOC_STACK; lia) ltac:(lia) G2 ltac:(csr; reflexivity) G9 G18 G19 ltac:(intros; reflexivity) Gb1 Hb' Lbilf Gl1 ltac:(lia) Llsf Hh
           R56m R96m LFr DSTl ltac:(intros k Hk; apply LFf; lia) ltac:(intros k Hk; lia) ltac:(intros; reflexivity) (POSTM_refl _ _ _ _)
           ltac:(rewrite with_vmmaps_vmmaps; apply roomtr_refl; lia)).
  intros Ag mg vmg rgg HWg G2' G4' G9' Grest Lg LEQg PMg RTg.
  change (forall r, In r [3; 4; 8; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rgg r = getr rg r) in Grest.
  assert (T10 : (0 + Z.of_nat 10 = 10)%Z) by reflexivity.
  rewrite with_vmmaps_twice in HWg |- *.
  assert (SUBg : sub_live Ag Af).
  { intros q k Hq. destruct (fin_dec (bw_linesf b) 10 0 q) as [(k' & Hk & E) | NE].
    - subst q. rewrite (Lg k' ltac:(lia)) in Hq. discriminate Hq.
    - rewrite <- (LEQg q ltac:(intros k' Hk'; apply NE; lia)). exact Hq. }
  assert (NLF : forall q k, live Ac3 q = Some k -> forall k', (0 <= k' < 10)%Z -> q <> Z_to_bv 64 (bw_linesf b k')).
  { intros q k Lq k' Hk' E. subst q. rewrite (N3lf k' Hk') in Lq. discriminate Lq. }
  assert (NLFr : forall q k, live Ar q = Some k -> forall k', (0 <= k' < 10)%Z -> q <> Z_to_bv 64 (bw_linesf b k')).
  { intros q k Lq k' Hk' E. subst q. destruct (LFk k' Hk') as (_ & _ & X & _). rewrite X in Lq. discriminate Lq. }
  assert (Lpxg : live Ag (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQg _ (NLFr _ _ Lrpx)); exact Lpxf).
  assert (Lbilg : live Ag (Z_to_bv 64 bil) = Some 104%Z) by (rewrite (LEQg _ (NLF _ _ L3bil)); exact Lbilf).
  assert (Llsg : live Ag (Z_to_bv 64 (bw_ls b)) = Some 80%Z).
  { rewrite (LEQg _ ltac:(intros k' Hk'; destruct (LFk k' Hk') as (G0 & _ & _ & _ & NEk' & _); apply zneq_w; [exact Gls | exact G0 | exact (not_eq_sym NEk')])). exact Llsf. }
  pose proof (bd_keep_postm C A Af Ag m M1 mf mg (with_vmmaps vmg md) s bil pixs (hdv w h 8 0 datas) CK HWg ltac:(lia) ltac:(lia) Gp0 Gp64 BKf PMg SUBg Lpxg) as BKg.
  pose proof (bd_thru_postm C Ag mf m mg s bil BTf PMg Lbilg Gb1 ltac:(lia)) as BTg.
  assert (R96g : rdn SEGS mg (Z_to_bv 64 (bil + 96)) 8 = Some (Z_to_le_bytes 8 (bw_ls b))) by (rewrite BTg by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact R96).
  apply (bd_free1 C A m M1 md Ag mg vmg rgg s bil pixs (bw_ls b) 80 240420 240428 (hdv w h 8 0 datas) S _ CK HWg Hs16 ltac:(lia) ltac:(lia) Gp0 Gp64 BKg G2' G4' Llsg N0ls NElsp
           ltac:(red; apply bv_eq; reflexivity) (bl_I al_rom fx rgg mg s bil (bw_ls b) Hs' Gb1 Hb' Gls R96g G2' G9')).
  { intros fin (r1' & M' & -> & -> & Q1' & _ & _ & Q10' & AG'). exists r1'. auto. }
  intros Ah mh vmh rh HWh CSh BKh PMh Llsh LEQh SUBh RTh.
  assert (Lbilh : live Ah (Z_to_bv 64 bil) = Some 104%Z) by (rewrite (LEQh _ (not_eq_sym NElsb)); exact Lbilg).
  assert (H2h : getr rh 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (H4h : getr rh 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  assert (H9h : getr rh 9 = Z_to_bv 64 bil) by (csr; reflexivity).
  apply (bd_free1 C A m M1 md Ah mh vmh rh s bil pixs bil 104 240428 240436 (hdv w h 8 0 datas) S _ CK HWh Hs16 ltac:(lia) ltac:(lia) Gp0 Gp64 BKh H2h H4h Lbilh N0bil NEbp
           ltac:(red; apply bv_eq; reflexivity) (bl_J al_rom fx rh mh s bil Hs' Gb1 Hb' H2h H9h)).
  { intros fin (r1' & M' & -> & -> & Q1' & _ & Q10' & AG'). exists r1'. auto. }
  intros Ai mi vmi ri HWi CSi BKi PMi Lbili LEQi SUBi RTi.
  assert (H2i : getr ri 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (H8i : getr ri 8 = Z_to_bv 64 pp) by (csr; reflexivity).
  assert (SOKpp : store_ok SEGS mi (Z_to_bv 64 pp) 8 = true) by exact (W_sok_win C Ai mi (with_vmmaps vmi md) pp 8 CK HWi ltac:(lia) ltac:(cbn; lia)).
  pose proof BKi as (_ & _ & KEEPi & SLOTi & FRMi & PXi).
  assert (K8 : rdn SEGS mi (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1))) by (rewrite SLOTi by lia; exact S8).
  assert (K16 : rdn SEGS mi (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (rewrite SLOTi by lia; exact S16).
  assert (K24 : rdn SEGS mi (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (rewrite SLOTi by lia; exact S24).
  assert (K32 : rdn SEGS mi (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18))) by (rewrite SLOTi by lia; exact S32).
  assert (K40 : rdn SEGS mi (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19))) by (rewrite SLOTi by lia; exact S40).
  destruct (bl_K al_rom fx ri mi s pp ret (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) Hs' Hspp ltac:(lia) Hret H1 SOKpp K8 K16 K24 K32 K40 H2i H8i)
    as (fink & RUNK & rk & Mk & -> & RIk & Rppk & K2' & K8' & K9' & K18' & K19' & AGk).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWi)) | exact (mp_lazy _ (w_pure _ _ _ _ HWi)) | exact RUNK |].
  assert (NOTpp : forall a : word, (u a < pp)%Z \/ (pp + 8 <= u a)%Z -> Mk a = mi a).
  { intros a Ha. apply (proj2 RIk). intros r [<-|[]]. unfold inreg. cbn [fst snd]. lia. }
  assert (SIg : sub_live Ai Ag) by (eapply sub_live_trans; [exact SUBi | exact SUBh]).
  assert (SIf : sub_live Ai Af) by (eapply sub_live_trans; [exact SIg | exact SUBg]).
  assert (SIe : sub_live Ai Ae) by (eapply sub_live_trans; [exact SIf | exact SUBf]).
  assert (SIc : sub_live Ai Ac) by (eapply sub_live_trans; [exact SIe | exact SUBe]).
  assert (SIb : sub_live Ai Ab) by (eapply sub_live_trans; [exact SIc | exact SUBc]).
  assert (SIa : sub_live Ai Aa) by (eapply sub_live_trans; [exact SIb | exact SUBb]).
  assert (SI4 : sub_live Ai A4) by (eapply sub_live_trans; [exact SIa | exact SUBa]).
  assert (SBi : sub_live Ai A3) by (eapply sub_live_trans; [exact SI4 | exact SUB4]).
  apply (HK Ai Mk vmi rk).
  - exact (proj1 (rinv_WP2 C Ai Ai mi (with_vmmaps vmi md) Mk [(pp, 8%Z)] (c_top C) CK HWi (sub_live_refl Ai) ltac:(lia) RIk
                   ltac:(constructor; [left; cbn [fst snd]; lia | constructor]))).
  - intros r Hr. destruct (cs_cases r Hr) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]; subst r; csr; reflexivity.
  - intros q HB. unfold bil_blocks in HB. destruct HB as [IN | (i & Hi & [E|[E|E]])].
    + cbn [map In] in IN.
      destruct IN as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst q.
      * exact Lbili.
      * exact (bdt_none Ai Ac _ SIc Lcx).
      * exact (bdt_none Ai Ae _ SIe Lex).
      * exact (bdt_none Ai Af _ SIf Lfx).
      * exact (bdt_none Ai Aa _ SIa Lax).
      * exact (bdt_none Ai Ab _ SIb Lbx).
      * exact (bdt_none Ai A3 _ SBi Lbsc3).
      * exact (bdt_none Ai A3 _ SBi Ldat3).
      * apply (bdt_none Ai A4 _ SI4). apply GONE4. left. unfold PA4. cbn [map In]. repeat (first [left; reflexivity | right]).
      * apply (bdt_none Ai A4 _ SI4). apply GONE4. left. unfold PA4. cbn [map In]. repeat (first [left; reflexivity | right]).
      * apply (bdt_none Ai A4 _ SI4). apply GONE4. left. unfold PA4. cbn [map In]. repeat (first [left; reflexivity | right]).
      * apply (bdt_none Ai A4 _ SI4). apply GONE4. left. unfold PA4. cbn [map In]. repeat (first [left; reflexivity | right]).
      * exact (bdt_none Ai Ah _ SUBi Llsh).
    + subst q. apply (bdt_none Ai A4 _ SI4). apply GONE4. right. exists i. exact (conj Hi (or_introl eq_refl)).
    + subst q. apply (bdt_none Ai A4 _ SI4). apply GONE4. right. exists i. exact (conj Hi (or_intror eq_refl)).
    + subst q. exact (bdt_none Ai Ag _ SIg (Lg i Hi)).
  - intros q NB.
    assert (NX : forall X, In X (map (Z_to_bv 64) [bil; bw_nc b; bw_kx b; bw_kf b; bw_spat b; bw_rng b; bw_bsc b; bw_datas b; bw_pa b; bw_parr b; bw_ba b; bw_barr b; bw_ls b]) -> q <> X)
      by (intros X HX E; apply NB; left; subst X; exact HX).
    rewrite (LEQi _ ltac:(apply NX; cbn [map In]; repeat (first [left; reflexivity | right]))), (LEQh _ ltac:(apply NX; cbn [map In]; repeat (first [left; reflexivity | right]))).
    rewrite (LEQg _ ltac:(intros k Hk E; apply NB; right; exists k; exact (conj Hk (or_intror (or_intror E))))).
    rewrite (LEQf _ ltac:(apply NX; cbn [map In]; repeat (first [left; reflexivity | right]))), (LEQe _ ltac:(apply NX; cbn [map In]; repeat (first [left; reflexivity | right]))), (LEQc _ ltac:(apply NX; cbn [map In]; repeat (first [left; reflexivity | right]))),
            (LEQb _ ltac:(apply NX; cbn [map In]; repeat (first [left; reflexivity | right]))), (LEQa _ ltac:(apply NX; cbn [map In]; repeat (first [left; reflexivity | right]))).
    assert (XX : ~ pd_gone (bw_pa b) (bw_parr b) (bw_ba b) (bw_barr b) (bw_pixes b) (bw_datad b) q).
    { intros [IN | (i & Hi & E)]; apply NB.
      { left. unfold PA4 in IN. cbn [map In] in IN |- *. tauto. }
      { right. exists i. split; [exact Hi|]. destruct E as [E|E]; [left | right; left]; exact E. } }
    rewrite (LEQ4 _ XX).
    apply LEQ3; apply NX; cbn [map In p_data hdv]; repeat (first [left; reflexivity | right]).
  - split.
    + apply (FRM_trans C (pp + 8) m mi Mk).
      * exact (FRM_mono C s (pp + 8) m mi FRMi ltac:(lia)).
      * intros a _ _ _ _ NS. apply NOTpp. unfold scratch in NS. lia.
    + intros q k i Lq Hi NP.
      assert (NEqb : q <> Z_to_bv 64 bil) by exact (live_neq _ _ _ _ Lq Lbili).
      assert (Lq' : live Ai (Z_to_bv 64 (u q)) = Some k) by (rewrite Z_to_bv_bv_unsigned; exact Lq).
      pose proof (u64_range q) as Rq.
      destruct (exW_blk_rng C Ai mi (with_vmmaps vmi md) (u q) k CK HWi Lq' ltac:(lia) ltac:(lia)) as (Qq1 & Qq2 & Qq3).
      assert (Uat : u (at_ q i) = (u q + i)%Z) by (apply at_u; lia).
      rewrite (NOTpp (at_ q i)) by lia.
      apply (KEEPi q k (at_ q i) Lq NEqb); lia.
  - intros a Ha. rewrite (NOTpp a ltac:(lia)). exact (FRM_byte_above C s m mi a CK FRMi ltac:(lia) ltac:(lia)).
  - apply (PIXat_frame mi Mk pixs _ PXi). intros x Hx. apply NOTpp. lia.
  - exact Rppk.
  - pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RTfz RTg ltac:(lia) ltac:(lia)) as R1. cbn [Z.add] in R1.
    pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 R1 RTh ltac:(lia) ltac:(lia)) as R2. cbn [Z.add] in R2.
    pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 R2 RTi ltac:(lia) ltac:(lia)) as R3. cbn [Z.add] in R3.
    exact R3.
Qed.

End BilDW.
