(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp FseReadSound HufPure_FseReadBridge HufPure_FseDecompRT.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AF_fse_rd_iface
     AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AF_huf_fdw_seg AF_huf_tbl_iface AF_huf_tbl_iface2 Stdio_kit AHarness_iface
     AF_huf_fdw_kit AF_huf_bdt_kit AF_huf_fdw_top1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require ABytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_fdw_tk RF_huf_bdt_model RF_huf_fdw_sm RF_huf_tbl_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_fdw_top2 () := "C46Stdlib5Lists4List2InC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC47Corelib4Init5Logic8eq_transC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List8map_consK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00c5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top24finvK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K47Corelib7Numbers7BinNums1Z02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top14PAGfC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg4FRBfC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg4SPAfK47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef6repeatC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompCfse_decompress_wkspC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top15dresAC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_tbl_iface2@fse_decomp_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1:spaf_propsC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K46Stdlib9micromega7EnvRing5PExpr01C5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top19fdw_closeC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg4FDSHI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HII47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1>FDW_OPEN_STACKI5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dt_fastModeC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dt_tableLogC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8dt_cellsC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_sm8cells_okI47Corelib4Init5Logic2or00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell03C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List6concatC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface5hblk8I47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface4bufHC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface7zshadowC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rhiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit7shcleanC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top17dres_okC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linK47Corelib4Init5Logic2or02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface@zshadow_of_hblk8C5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface<rng_of_hblk8C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5nshadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedK47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm?bufA_unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_rtcellsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8artcellsC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_mem@rd_rw_cells_appAC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompFdecompress_usingDTableC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission5BothW5ABase>ablk_disj_bandC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm@stack_not_clientC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asmAmagree_munch_stepK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=stk_transportc5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top29fdw_exit0C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit>rclean_shcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6hull64C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7app_blkC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_subC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit;zshadow_subC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow9nshad_divC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC35stdpp4base6lookupC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowC47Corelib4Init9Datatypes3appK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5dcell00I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00K46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6dtable00C5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_tbl_iface>fse_cell_bytesC5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_tbl_iface29ABIT_MASKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSK47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_tbl_iface2;AZEROFILLEDK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top19DEC_STACKC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_tbl_iface<fse_dt_bytesC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT9dtable_okC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompJFSE_BUILD_DTABLE_WKSP_SIZEC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp?FSE_DTABLE_SIZEC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1;dtok_cellsAC46Stdlib5Lists4List9app_assocC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model9u8arr_appC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le2C5ARocqVerifyHarness?AgentSubmission3Lib3ArrArw_cells_of_u8arrC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC46Stdlib5Lists4List9app_nil_rC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure?rw_cells_recastC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<shad_in_bandC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm9cl_shadowC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm8cl_blockC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm9aca_monoAC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree;magree_monoC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree<magree_transC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?rw_cells_magreeK4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6ltb_geK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4chkZC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3sxbC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib3MemAsext_extract_byteC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit7acc_shZC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx16C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le2C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree:stk_magreeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface;shad_unshadC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?bytes_at_magreeC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm8u8arr_mgC46Stdlib5Lists4List<firstn_skipnC46Stdlib5Lists4List7map_appC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_appC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3minC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init3Nat3subC46Stdlib5Lists4List<length_skipnC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit;shclean_subC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow>unpoisoned_subC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kitFzshadow_of_unpoisoned8C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit>shclean_magreeC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit>zshadow_magreeC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT<Forall_skipnC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas@Forall_all_bytesC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRTKdecompress_usingDTable_safeK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02c5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top27fdw_decC5ARocqVerifyHarness?AgentSubmission5Plain>RF_huf_tbl_kit8zx16_litC47Corelib5Lists7ListDef5skipnC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C47Corelib4Init5Logic7f_equalC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z3maxK4ELinuxProcessSemantics5Riscv5Instr5aluop01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5msize02I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind00C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit4sxb0C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount;read_ncountC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C46Stdlib5Lists4List=repeat_lengthC5ARocqVerifyHarness?AgentSubmission4SpecEHufPure_FseReadBridge@read_ncount_safeC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT9ncount_okC5ARocqVerifyHarness?AgentSubmission4Spec<FseReadSoundAread_ncount_totalC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;Z_to_bv_eqmC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompHFSE_DECOMPRESS_WKSP_SIZEC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount6assertC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT3nclK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sllwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_sllwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sllC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sllC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiC56Stdlib6ZArith6BinInt1Z7div_posC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp<build_dtableC46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT?build_dtable_okC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_tk9rt_shortsC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr03C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_kit:land64_modC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC56Stdlib6ZArith6BinInt1Z:shiftl_1_lC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface?fse_build_postAC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init9Datatypes?andb_true_introC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT;assert_truec5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top2:fdw_bd_retC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8evtF_cutC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1:wksp_machAC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1=wksp_machA_okC5ARocqVerifyHarness?AgentSubmission6Common7SFModel<mod64_land63K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure:sx32_smallC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4wsumC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT4wsumC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompDFSE_MAX_SYMBOL_VALUEK4ELinuxProcessSemantics5Riscv5Instr5msize03C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountBZSTD_error_GENERICC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountLZSTD_error_tableLog_tooLargeC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount@FSE_MIN_TABLELOGC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountIFSE_TABLELOG_ABSOLUTE_MAXK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount@FSE_MAX_TABLELOGC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface@AFSE_BUILD_STACK".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Notation FB0 F := (mkABlock (ABFake 0) F 64).
(* [comment removed for export] *)
Local Notation PAGf := (AF_huf_fdw_top1.PAGf AI).
Local Notation fdw_close := (AF_huf_fdw_top1.fdw_close AI fflag FFLAG FREL).
Local Notation mg_after_call := (AF_huf_fdw_top1.mg_after_call AI).
Local Notation pag_rd := (AF_huf_fdw_top1.pag_rd AI).

Definition hideF (P : Prop) : Prop := P.

Section After.
  Variables (L : alayout) (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (m : amem) (st : astate) (LB : list ablock) (SPV DST dcap S W wks maxLog lo FF : Z) (src : list Z).
  Hypothesis LBH : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis F64 : FF mod 64 = 0.
  Hypothesis FH : ablk FF (FF + 64).
  Hypothesis FC : FF + 64 <= ATOP.
  Hypothesis RFF : rng RNG FF 64.
  Hypothesis RSFF : rng RNG (shad FF) 8.
  Hypothesis FFD : forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LO : lo <= SPV - AFSE_DECOMP_STACK.
  Hypothesis SPT : SPV + 16 < al_top L.
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis HDST : hblk8 LB DST dcap.
  Hypothesis DC : 0 <= dcap <= 255.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis BDT : fse_build_stmtA AI.
  Variable rstk : region.
  Hypothesis RCL : rclean m rstk.
  Hypothesis RLO' : r_lo rstk <= lo.
  Hypothesis RHI' : SPV <= r_hi rstk.
  Hypothesis RRLO : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis ZMK : zshadow m ABIT_MASK 128.
  Hypothesis MKCI : forall a, ABIT_MASK <= a < ABIT_MASK + 128 -> in_ranges CI a.
  Hypothesis SAFE : dec_stmtA 0x98664 0 false.
  Hypothesis FAST : dec_stmtA 0x984e8 1 true.
  Notation POST := (fse_decomp_postA AI L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV DST dcap W wks maxLog src lo m).

  (* [comment removed for export] *)
  Definition finv (mx : amem) (j0' j32 j48 : list byte) : Prop :=
    AHEAP AI L RNG st (FB0 FF :: LB) mx /\ magree bsegs (PAGf LB SPV DST dcap W wks) m mx /\ mem_inv bsegs mx
    /\ rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) FDSH
    /\ rw_cells bsegs mx FF [C8 (Z_to_bv 64 0x41b58ab3)] /\ rw_cells bsegs mx (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))]
    /\ rw_cells bsegs mx (SPV + -104) (FRBf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ rw_cells bsegs mx (SPAf SPV) [CB 32 j0'; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880);
                                     CB 8 j32; C8 (Z_to_bv 64 FF); CB 72 j48]
    /\ stk bsegs mx lo (SPAf SPV) /\ stk bsegs mx (SPAf SPV + 152) (SPV + -104).

  Lemma finv_transport : forall mx m5 j0' j32 j48 (P : Z -> Prop),
    finv mx j0' j32 j48 ->
    AHEAP AI L RNG st (FB0 FF :: LB) m5 -> mem_inv bsegs m5 -> stk bsegs m5 lo (SPAf SPV) -> magree bsegs P mx m5 ->
    (forall a, PAGf LB SPV DST dcap W wks a -> P a) -> (forall a, SPAf SPV <= a < SPV -> P a) ->
    (forall a, FF <= a < FF + 64 -> P a) -> (forall a, Z.shiftr FF 3 + 2147450880 <= a < Z.shiftr FF 3 + 2147450880 + 8 -> P a) ->
    finv m5 j0' j32 j48.
  Proof.
    intros mx m5 j0' j32 j48 P (AHx & MGx & MIx & SHx & F0x & F56x & FRBx & FRAx & STLx & STGx) AH5 MI5 STL5 MG5 HP1 HP2 HP3 HP4.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
    refine (conj AH5 (conj _ (conj MI5 (conj _ (conj _ (conj _ (conj _ (conj _ (conj STL5 _))))))))).
    - eapply magree_trans; [exact MGx|]. eapply magree_mono; [exact MG5| exact HP1].
    - eapply rw_cells_magree; [exact MG5| exact SHx|]. intros a Ha. apply HP4. cbn in Ha. lia.
    - eapply rw_cells_magree; [exact MG5| exact F0x|]. intros a Ha. apply HP3. cbn in Ha. lia.
    - eapply rw_cells_magree; [exact MG5| exact F56x|]. intros a Ha. apply HP3. cbn in Ha. lia.
    - eapply rw_cells_magree; [exact MG5| exact FRBx|]. intros a Ha. apply HP2. cbn in Ha. lia.
    - eapply rw_cells_magree; [exact MG5| exact FRAx|]. intros a Ha. apply HP2. cbn in Ha. lia.
    - eapply stk_magree; [exact MG5| exact STGx|]. intros a Ha. apply HP2. lia.
  Qed.

Lemma shad_inv8 : forall s, shad (8 * (s - ASHOFF)) = s.
Proof. intros s. rewrite shad_div. Z.div_mod_to_equations. lia. Qed.

Lemma sh_hblk_out : forall LB0 X n Y k a', hblk8 LB0 X n -> (forall b, In b LB0 -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  X <= Y -> Y + k <= X + n -> 0 <= a' < 2^47 -> ~ (Y <= shad a' < Y + k).
Proof.
  intros LB0 X n Y k a' (p & A & N & HIn & _ & H1 & H2) HL HY HK Ha. pose proof (HL _ HIn) as HB. cbn [ab_addr ab_size] in HB.
  rewrite shad_div. unfold ablk, AIMG_HI, KLS in HB. unfold ASHOFF. Z.div_mod_to_equations. lia.
Qed.

Lemma ffsh_pre : forall F a, F mod 64 = 0 -> 0 <= F -> Z.shiftr F 3 + ASHOFF <= a < Z.shiftr F 3 + ASHOFF + 8 ->
  F <= 8 * (a - ASHOFF) < F + 64.
Proof. intros F a H0 H1 Ha. rewrite Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha. Z.div_mod_to_equations. lia. Qed.

Lemma shrange_pre : forall x y s, shad x <= s < shad y -> x mod 8 = 0 -> x <= 8 * (s - ASHOFF) < y.
Proof. intros x y s Hs H0. rewrite !shad_div in Hs. Z.div_mod_to_equations. lia. Qed.

Lemma rng_bufH : forall L0 RNG0 st0 LB0 m0 B n, AHEAP AI L0 RNG0 st0 LB0 m0 -> bufH LB0 B n -> 0 <= n ->
  rng RNG0 B n /\ rng RNG0 (shad B) (nshad (n + B mod 8)).
Proof.
  intros L0 RNG0 st0 LB0 m0 B n AH (p & A & N & HIn & H1 & H2) Hn.
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIn) as (_ & (_ & _ & _ & A16) & RA & RSA & _).
  split; [eapply rng_sub; [exact RA| lia| lia]|].
  eapply rng_sub; [exact RSA| |]; unfold nshad, shlen; rewrite ?shad_div, ?Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia.
Qed.

Lemma shad_lt_atop : forall a, 0 <= a < 2^47 -> shad a < ATOP.
Proof. intros a Ha. pose proof atop_range as ATR. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. Qed.

Lemma rw_cells_eqA : forall m0 A A' cs, A = A' -> rw_cells bsegs m0 A cs -> rw_cells bsegs m0 A' cs.
Proof. intros m0 A A' cs -> H. exact H. Qed.

Lemma wsum_elem_le : forall l, Forall (fun c => -1 <= c) l -> Forall (fun c => c <= HufPure_FseDecompRT.wsum l) l.
Proof.
  induction l as [|c t IH]; intros H; [constructor|].
  inversion H as [|? ? Hc Ht]; subst.
  pose proof (HufPure_FseDecompRT.wsum_nonneg t Ht) as Wt.
  specialize (IH Ht). cbn [HufPure_FseDecompRT.wsum].
  assert (Hw : c <= HufPure_FseDecompRT.wt c /\ 0 <= HufPure_FseDecompRT.wt c)
    by (unfold HufPure_FseDecompRT.wt; destruct (Z.eqb_spec c (-1)); lia).
  constructor; [lia|]. eapply Forall_impl; [|exact IH]. intros x Hx; cbv beta in *; lia.
Qed.

Lemma rt_bounds : forall (rt : list Z) msv tl, length rt = 256%nat -> 0 <= msv <= 255 -> 0 <= tl <= 12 ->
    (forall i, 0 <= i <= msv -> -1 <= FseNCount.Znth i rt) -> FseNCount.wsum (firstn (Z.to_nat (msv + 1)) rt) = 2^tl ->
    (forall i, msv < i <= 255 -> FseNCount.Znth i rt = 0) -> Forall (fun c => -1 <= c <= 2^12) rt.
Proof.
  intros rt msv tl LN MS TL HL WS HZ.
  assert (LP : length (firstn (Z.to_nat (msv + 1)) rt) = Z.to_nat (msv + 1)) by (rewrite length_firstn; lia).
  assert (EN : forall i, (i < Z.to_nat (msv + 1))%nat -> nth i (firstn (Z.to_nat (msv + 1)) rt) 0 = nth i rt 0).
  { intros i Hi. rewrite <- (firstn_skipn (Z.to_nat (msv + 1)) rt) at 2. rewrite app_nth1 by lia. reflexivity. }
  assert (FP : Forall (fun c => -1 <= c) (firstn (Z.to_nat (msv + 1)) rt)).
  { apply Forall_nth. intros i d Hi. rewrite LP in Hi. rewrite (nth_indep _ d 0) by lia. rewrite EN by lia.
    pose proof (HL (Z.of_nat i) ltac:(lia)) as H1. unfold FseNCount.Znth in H1. rewrite Nat2Z.id in H1. exact H1. }
  pose proof (wsum_elem_le _ FP) as FU. rewrite HufPure_FseReadBridge.wsum_eq, WS in FU.
  pose proof (Z.pow_le_mono_r 2 tl 12 ltac:(lia) ltac:(lia)) as P12.
  apply Forall_nth. intros i d Hi. rewrite (nth_indep _ d 0) by lia.
  destruct (Nat.lt_ge_cases i (Z.to_nat (msv + 1))) as [Hlt|Hge].
  - rewrite <- EN by lia. rewrite Forall_nth in FP, FU. specialize (FP i 0 ltac:(lia)). specialize (FU i 0 ltac:(lia)).
    cbv beta in FP, FU. lia.
  - pose proof (HZ (Z.of_nat i) ltac:(lia)) as H1. unfold FseNCount.Znth in H1. rewrite Nat2Z.id in H1. rewrite H1. lia.
Qed.

Lemma wksp_norm : forall tl msv X, 5 <= tl <= 12 -> 0 <= msv <= 255 ->
  X = 2^tl * 4 + 1 * 2^tl + 2 * (msv + 1) + 19 ->
  X - X mod 4 + 516 = FSE_DECOMPRESS_WKSP_SIZE tl msv.
Proof.
  intros tl msv X TL MS ->. clear - TL MS. unfold FSE_DECOMPRESS_WKSP_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE, FSE_MAX_SYMBOL_VALUE.
  replace (2^tl) with (2^(tl - 5) * 32) by (change 32 with (2^5); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (0 < 2^(tl - 5)) by (apply Z.pow_pos_nonneg; lia).
  set (Q := 2^(tl - 5)) in *. Z.div_mod_to_equations. lia.
Qed.

Lemma land_m63 : forall x, 0 <= x < 2^63 -> Z.land x (2^63 - 4) = x - x mod 4.
Proof.
  intros x Hx. clear - rc Hx.
  replace (2^63 - 4) with (Z.land (Z.ones 63) (2^64 - 2^2)) by (vm_compute; reflexivity).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite land_align_downA by lia. reflexivity.
Qed.

Lemma u8arr_sub2 : forall m0 A (l : list byte) k1 k2, (k1 + k2 <= length l)%nat -> u8arr bsegs m0 A l ->
  u8arr bsegs m0 A (firstn k1 l) /\ u8arr bsegs m0 (A + Z.of_nat k1) (firstn k2 (skipn k1 l)).
Proof.
  intros m0 A l k1 k2 Hk U.
  rewrite <- (firstn_skipn k1 l) in U. apply RF_huf_bdt_model.u8arr_app in U as (U1 & U2).
  rewrite length_firstn, Nat.min_l in U2 by lia. split; [exact U1|].
  rewrite <- (firstn_skipn k2 (skipn k1 l)) in U2. apply RF_huf_bdt_model.u8arr_app in U2 as (U3 & _). exact U3.
Qed.

Lemma hblk8_sub : forall LB0 b X n Y k, hblk8 LB0 X n -> X <= Y -> Y + k <= X + n -> hblk8 (b :: LB0) Y k.
Proof.
  intros LB0 b X n Y k (p & A0 & N0 & HIn & HN & HA & HB) H1 H2. exists p, A0, N0. split; [right; exact HIn| lia].
Qed.

Local Ltac fdw_kc K := exfalso; rewrite ?Z.mod_small in K by lia;
  repeat match type of K with
  | context [?a <? ?b] => first [rewrite (proj2 (Z.ltb_lt a b)) in K by lia | rewrite (proj2 (Z.ltb_ge a b)) in K by lia]
  | context [?a =? ?b] => first [rewrite (proj2 (Z.eqb_eq a b)) in K by lia | rewrite (proj2 (Z.eqb_neq a b)) in K by lia]
  end; first [lia | vm_compute in K; congruence].




  (* [comment removed for export] *)
  Lemma fdw_exit : forall mx j0' j32 j48 rv
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    finv mx j0' j32 j48 -> dresA DST dcap (fse_decompress_wksp (repeat 0 256) dcap src maxLog wks) mx rv -> 0 <= rv < 2^64 ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (SPAf SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV)) (Z_to_bv 64 rv)
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31)
          FR (Z_to_bv 64 0x98318) fc None mx (seg_rom bsegs)).
Proof.
  intros mx j0' j32 j48 rv x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    (AHx & MGx & MIx & SHx & F0x & F56x & FRBx & FRAx & STLx & STGx) DR RV.
  pose proof atop_range as ATR. unfold AFSE_DECOMP_STACK in LO.
  pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
  zstep. zstep.
  destruct HDST as (p & A0 & N0 & HIn & _ & HA0 & HA1).
  eapply (fdw_close L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m mx st LB SPV DST dcap W wks maxLog lo FF rv src);
    first [exact AHx| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact MGx| exact MIx| exact SHx
    | exact F0x| exact F56x| exact FRBx| exact FRAx| reflexivity| exact STLx| exact STGx| exact BOT| exact SPT| exact SP16| exact RSTK
    | exact (ex_intro _ p (ex_intro _ A0 (ex_intro _ N0 (conj HIn (conj HA0 HA1)))))| exact DR| exact RV| unfold FDW_OPEN_STACK; lia| lia].
Qed.

  (* [comment removed for export] *)
  Lemma fdw_exit0 : forall mx j0' j32 j48 rv
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    finv mx j0' j32 j48 -> dresA DST dcap (fse_decompress_wksp (repeat 0 256) dcap src maxLog wks) mx rv -> 0 <= rv < 2^64 ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (SPAf SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) x9 (Z_to_bv 64 rv) x11 x12 x13 x14 x15
               (Z_to_bv 64 FF) x17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31)
          FR (Z_to_bv 64 0x98320) fc None mx (seg_rom bsegs)).
Proof.
  intros mx j0' j32 j48 rv x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    (AHx & MGx & MIx & SHx & F0x & F56x & FRBx & FRAx & STLx & STGx) DR RV.
  pose proof atop_range as ATR. unfold AFSE_DECOMP_STACK in LO.
  destruct HDST as (p & A0 & N0 & HIn & _ & HA0 & HA1).
  eapply (fdw_close L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m mx st LB SPV DST dcap W wks maxLog lo FF rv src);
    first [exact AHx| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact MGx| exact MIx| exact SHx
    | exact F0x| exact F56x| exact FRBx| exact FRAx| reflexivity| exact STLx| exact STGx| exact BOT| exact SPT| exact SP16| exact RSTK
    | exact (ex_intro _ p (ex_intro _ A0 (ex_intro _ N0 (conj HIn (conj HA0 HA1)))))| exact DR| exact RV| unfold FDW_OPEN_STACK; lia| lia].
Qed.

  Lemma fdw_call : forall PC fm fast mz j0' j32 j48 (d : dtable) (S0 : Z) (bs : list Z) (jd : list byte)
      (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    dec_stmtA PC fm fast -> dt_fastMode d = fm -> fast = negb (fm =? 0) ->
    finv mz j0' j32 j48 ->
    fse_decompress_wksp (repeat 0 256) dcap src maxLog wks = decompress_usingDTable bs d dcap fast ->
    5 <= dt_tableLog d <= 12 -> zlen (dt_cells d) = 2^(dt_tableLog d) -> RF_huf_fdw_sm.cells_ok (dt_tableLog d) (dt_cells d) ->
    rw_cells bsegs mz (W + 512) [C2 (Z_to_bv 64 (dt_tableLog d)); C2 (Z_to_bv 64 fm)] ->
    bytes_at bsegs mz (W + 512 + 4) (concat (map fse_cell_bytes (dt_cells d))) ->
    hblk8 LB W wks -> W mod 8 = 0 -> 512 + 4 + 4 * 2^(dt_tableLog d) <= wks ->
    bytes_at bsegs mz S0 (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs -> zlen bs <= 65536 -> 16 <= S0 ->
    bufH LB S0 (zlen bs) ->
    u8arr bsegs mz DST jd -> zlen jd = dcap ->
    (DST + dcap <= S0 \/ S0 + zlen bs <= DST) -> (DST + dcap <= W \/ W + wks <= DST) -> (S0 + zlen bs <= W \/ W + wks <= S0) ->
    zshadow mz (SPAf SPV + 80) 72 -> shclean mz (SPAf SPV + 112) (SPAf SPV + 152) (r_rlo rstk) (r_rhi rstk) ->
    zshadow mz ABIT_MASK 128 ->
    dres_ok (decompress_usingDTable bs d dcap fast) ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (SPAf SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV)) x10
               x11 (Z_to_bv 64 (zlen bs)) x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
               (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (W + 512)) (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25
               (Z_to_bv 64 S0) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
          FR (Z_to_bv 64 PC) fc None mz (seg_rom bsegs)).
  Proof.
    intros PC fm fast mz j0' j32 j48 d S0 bs jd x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31
      HD FM FS FI DEQ TL CL CO DTH DTC HW W8 WKD SRC SRCF SRCL S16 SRCH JD JDL D1 D2 D3 ZF SC ZK DOK.
    pose proof atop_range as ATR. unfold AFSE_DECOMP_STACK in LO.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
    pose proof FI as (AHz & MGz & MIz & SHz & F0z & F56z & FRBz & FRAz & STLz & STGz).
    pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
    pose proof (AI_layout AI _ _ _ _ _ AHz) as (LY1 & LY2 & LY3 & _).
    pose proof (ablk_lin _ _ FH) as FHL.
    pose proof HW as (pW & AW & NW & HInW & HNW & HW1 & HW2).
    pose proof (ablk_lin _ _ (LBH _ HInW)) as WL. cbn [ab_addr ab_size] in WL.
    pose proof HDST as (pD & AD & ND & HInD & HND & HD1 & HD2).
    pose proof (ablk_lin _ _ (LBH _ HInD)) as DL. cbn [ab_addr ab_size] in DL. unfold AIMG_HI in DL.
    pose proof SRCH as (pS & AS & NS & HInS & HS1 & HS2).
    pose proof (ablk_lin _ _ (LBH _ HInS)) as SL. cbn [ab_addr ab_size] in SL.
    pose proof (FFD _ HInD) as FFDD. cbn [ab_addr ab_size] in FFDD.
    pose proof (rclean_shclean _ _ RCL) as SHC. pose proof (shclean_hull _ _ _ _ _ SHC) as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6).
    assert (ZL : 0 <= zlen bs) by lia.
    assert (TP : 0 < 2^(dt_tableLog d)) by (apply Z.pow_pos_nonneg; lia).
    assert (HW' : hblk8 (FB0 FF :: LB) W wks) by (exists pW, AW, NW; split; [right; exact HInW| lia]).
    assert (HD' : hblk8 (FB0 FF :: LB) DST dcap) by (exists pD, AD, ND; split; [right; exact HInD| lia]).
    assert (HS' : bufH (FB0 FF :: LB) S0 (zlen bs)) by (exists pS, AS, NS; split; [right; exact HInS| lia]).
    pose proof (zshadow_of_hblk8 AI _ _ _ _ _ _ _ AHz HW' ltac:(lia)) as ZW.
    pose proof (rng_of_hblk8 AI _ _ _ _ _ _ _ AHz HW' ltac:(lia)) as (RW & RSW).
    pose proof (zshadow_of_hblk8 AI _ _ _ _ _ _ _ AHz HD' ltac:(lia)) as ZD.
    pose proof (rng_of_hblk8 AI _ _ _ _ _ _ _ AHz HD' ltac:(lia)) as (RD & RSD).
    pose proof (rng_bufH _ _ _ _ _ _ _ AHz HS' ZL) as (RS & RSS).
    pose proof (bufA_unpoisoned AI _ _ _ _ _ _ _ AHz (bufA_of_bufH _ _ _ _ HS') ZL) as US.
    pose proof (proj1 (ABytes.rw_cells_app _ _ _ [CB 32 j0'] _) FRAz) as (P0 & R1).
    pose proof (proj1 (ABytes.rw_cells_app _ _ _ [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] _) R1)
      as (P32 & R2).
    pose proof (proj1 (ABytes.rw_cells_app _ _ _ [CB 8 j32; C8 (Z_to_bv 64 FF)] _) R2) as (P64 & P80).
    apply (rw_cells_eqA _ _ (SPAf SPV + 32)) in P32; [|reflexivity].
    apply (rw_cells_eqA _ _ (SPAf SPV + 64)) in P64; [|rewrite <- ?Z.add_assoc; reflexivity].
    apply (rw_cells_eqA _ _ (SPAf SPV + 80)) in P80; [|rewrite <- ?Z.add_assoc; reflexivity].
    clear R1 R2.
    eapply (HD RNG POST mz SPV FF DST dcap S0 (W + 512) lo (r_rlo rstk) (r_rhi rstk) bs d gp tp FR fc
             x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 j48 jd).
    - exact P32.
    - exact P80.
    - exact STLz.
    - exact BOT.
    - unfold DEC_STACK. lia.
    - exact SP16.
    - lia.
    - exact ZF.
    - exact SC.
    - exact RRS.
    - eapply rng_sub; [exact RSTK| lia| lia].
    - eapply rng_sub; [exact RRS| |]; rewrite !shad_div; Z.div_mod_to_equations; lia.
    - eapply rng_sub; [exact RSTK| lia| lia].
    - exact TL.
    - exact CL.
    - exact CO.
    - exact FM.
    - exact DTH.
    - exact DTC.
    - eapply ablk_sub; [exact (LBH _ HInW)| cbn [ab_addr ab_size]; lia| cbn [ab_addr ab_size]; lia].
    - Z.div_mod_to_equations. lia.
    - eapply zshadow_sub; [exact ZW| lia| lia].
    - eapply rng_sub; [exact RW| lia| lia].
    - eapply rng_sub; [exact RSW| |]; unfold nshad; rewrite ?shad_div, ?Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia.
    - exact SRC.
    - exact SRCF.
    - exact SRCL.
    - eapply ablk_sub; [exact (LBH _ HInS)| cbn [ab_addr ab_size]; lia| cbn [ab_addr ab_size]; lia].
    - lia.
    - exact S16.
    - exact US.
    - exact RS.
    - exact RSS.
    - exact DOK.
    - exact JD.
    - exact JDL.
    - exact DC.
    - eapply ablk_sub; [exact (LBH _ HInD)| cbn [ab_addr ab_size]; lia| cbn [ab_addr ab_size]; lia].
    - lia.
    - exact ZD.
    - exact RD.
    - exact RSD.
    - exact D1.
    - lia.
    - lia.
    - exact MIz.
    - exact (AI_rtcells AI _ _ _ _ _ AHz).
    - exact ZK.
    - eapply rng_sub; [exact RSTK| lia| lia].
    - exact RI.
    - exact RISH.
    - intros m1 rv j48' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
        MU WM MI1 STK1 C80 C32 DR RV.
      pose proof (magree_of_munch bsegs _ _ _ MU WM) as MGm.
      assert (FS8 : Z.of_nat (cells_size FDSH) = 8) by reflexivity.
      assert (FRS : Z.of_nat (cells_size (FRBf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) = 104) by reflexivity.
      assert (FI1 : finv m1 j0' j32 j48').
      { refine (conj _ (conj _ (conj MI1 (conj _ (conj _ (conj _ (conj _ (conj _ (conj STK1 _))))))))).
        - eapply (AI_frame AI _ _ _ _ mz m1 _ AHz MU WM).
          apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
          + left. left. split; lia.
          + left. left. split; lia.
          + right. left. exists (HB pD AD ND). split; [right; exact HInD| cbn [ab_addr ab_size]; lia].
        - eapply magree_munch_step; [exact MGz| exact MU| exact WM|].
          intros a (Ha & HnD & HnW). cbn [outside].
          refine (conj _ (conj _ (conj _ I))); intros Hr; [| | exact (HnD Hr)];
            exact (stack_not_client CI LB SPV lo a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha).
        - eapply rw_cells_magree; [exact MGm| exact SHz|]. intros a Ha. rewrite FS8 in Ha.
          pose proof (ffsh_pre FF a F64 ltac:(lia) Ha) as Ha'.
          pose proof (shad_lt_atop (8 * (a - ASHOFF)) ltac:(lia)) as Hs. rewrite shad_inv8 in Hs.
          pose proof (sh_hblk_out _ _ _ DST dcap (8 * (a - ASHOFF)) HDST LBH ltac:(lia) ltac:(lia) ltac:(lia)) as Hd.
          rewrite shad_inv8 in Hd.
          cbn [outside]. refine (conj _ (conj _ (conj Hd I))); intro; lia.
        - eapply rw_cells_magree; [exact MGm| exact F0z|]. intros a Ha. cbn in Ha.
          cbn [outside]. refine (conj _ (conj _ (conj _ I))); intro; lia.
        - eapply rw_cells_magree; [exact MGm| exact F56z|]. intros a Ha. cbn in Ha.
          cbn [outside]. refine (conj _ (conj _ (conj _ I))); intro; lia.
        - eapply rw_cells_magree; [exact MGm| exact FRBz|]. intros a Ha. rewrite FRS in Ha.
          cbn [outside]. refine (conj _ (conj _ (conj _ I))); intro; lia.
        - apply (proj2 (ABytes.rw_cells_app _ _ _ [CB 32 j0'] _)). split.
          { eapply rw_cells_magree; [exact MGm| exact P0|]. intros a Ha. cbn in Ha.
            cbn [outside]. refine (conj _ (conj _ (conj _ I))); intro; lia. }
          apply (rw_cells_eqA _ (SPAf SPV + 32)); [reflexivity|].
          apply (proj2 (ABytes.rw_cells_app _ _ _ [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] _)).
          split; [exact C32|].
          apply (rw_cells_eqA _ (SPAf SPV + 64)); [rewrite <- ?Z.add_assoc; reflexivity|].
          apply (proj2 (ABytes.rw_cells_app _ _ _ [CB 8 j32; C8 (Z_to_bv 64 FF)] _)). split.
          { eapply rw_cells_magree; [exact MGm| exact P64|]. intros a Ha. cbn in Ha.
            cbn [outside]. refine (conj _ (conj _ (conj _ I))); intro; lia. }
          apply (rw_cells_eqA _ (SPAf SPV + 80)); [rewrite <- ?Z.add_assoc; reflexivity|]. exact C80.
        - eapply stk_magree; [exact MGm| exact STGz|]. intros a Ha.
          cbn [outside]. refine (conj _ (conj _ (conj _ I))); intro; lia. }
      eapply (fdw_exit m1 j0' j32 j48' rv); [exact FI1| rewrite DEQ; exact DR| exact RV].
  Qed.


  (* [comment removed for export] *)
  Lemma fdw_dec : forall mz j0' j32 j48 (d : dtable) (S0 ncl : Z) (bs : list Z) (jd : list byte)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x28 x29 x30 x31 : word),
    finv mz j0' j32 j48 -> rw_cells bsegs mz (SPAf SPV + 24) [C8 (Z_to_bv 64 ncl)] ->
    (* [comment removed for export] *)
    fse_decompress_wksp (repeat 0 256) dcap src maxLog wks = decompress_usingDTable bs d dcap (negb (dt_fastMode d =? 0)) ->
    5 <= dt_tableLog d <= 12 -> zlen (dt_cells d) = 2^(dt_tableLog d) -> RF_huf_fdw_sm.cells_ok (dt_tableLog d) (dt_cells d) ->
    (dt_fastMode d = 0 \/ dt_fastMode d = 1) ->
    (* [comment removed for export] *)
    rw_cells bsegs mz (W + 512) [C2 (Z_to_bv 64 (dt_tableLog d)); C2 (Z_to_bv 64 (dt_fastMode d))] ->
    bytes_at bsegs mz (W + 512 + 4) (concat (map fse_cell_bytes (dt_cells d))) ->
    hblk8 LB W wks -> W mod 8 = 0 -> 512 + 4 + 4 * 2^(dt_tableLog d) <= wks ->
    (* [comment removed for export] *)
    bytes_at bsegs mz S0 (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs -> zlen bs <= 65536 -> 16 <= S0 ->
    bufH LB S0 (zlen bs) ->
    u8arr bsegs mz DST jd -> zlen jd = dcap ->
    (DST + dcap <= S0 \/ S0 + zlen bs <= DST) -> (DST + dcap <= W \/ W + wks <= DST) -> (S0 + zlen bs <= W \/ W + wks <= S0) ->
    (* [comment removed for export] *)
    zshadow mz (SPAf SPV + 80) 72 -> shclean mz (SPAf SPV + 112) (SPAf SPV + 152) (r_rlo rstk) (r_rhi rstk) ->
    zshadow mz ABIT_MASK 128 ->
    S0 = S + ncl -> zlen bs = zlen src - ncl -> 0 <= ncl -> 0 <= S ->
    dres_ok (decompress_usingDTable bs d dcap (negb (dt_fastMode d =? 0))) ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (SPAf SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV))
               (Z_to_bv 64 (W + 514)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (W + 512)) (Z_to_bv 64 dcap) (Z_to_bv 64 (zlen src))
               x23 x24 x25 (Z_to_bv 64 S0) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x98490) fc None mz (seg_rom bsegs)).
Proof.
  intros mz j0' j32 j48 d S0 ncl bs jd x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x28 x29 x30 x31
    FI C24 DEQ TL CL CO CF DTH DTC HW W8 WKD SRC SRCF SRCL S16 SRCH JD JDL D1 D2 D3 ZF SC ZK ES ZB NCL SN DOK.
  pose proof atop_range as ATR. unfold AFSE_DECOMP_STACK in LO.
  pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
  pose proof FI as (AHz & MGz & MIz & SHz & F0z & F56z & FRBz & FRAz & STLz & STGz).
  pose proof (proj1 (ABytes.rw_cells_app _ _ _ [CB 32 j0'; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] _) FRAz) as (_ & R1).
  pose proof (proj1 (ABytes.rw_cells_app _ _ _ [C8 (Z_to_bv 64 DST)] _) R1) as (C48 & _).
  replace (SPAf SPV + Z.of_nat (cells_size _)) with (SPAf SPV + 48) in C48 by reflexivity.
  pose proof (proj1 (ABytes.rw_cells_app _ _ _ [C2 (Z_to_bv 64 (dt_tableLog d))] _) DTH) as (_ & DTF).
  replace (W + 512 + Z.of_nat (cells_size _)) with (W + 514) in DTF by (cbn; lia).
  assert (HW' : hblk8 (FB0 FF :: LB) W wks)
    by (destruct HW as (p & A0 & N0 & HIn & HN & HA & HB); exists p, A0, N0; split; [right; exact HIn| lia]).
  assert (WB : 0 <= W /\ W + wks <= ATOP)
    by (destruct HW as (p & A0 & N0 & HIn & _ & HA & HB); pose proof (ablk_lin _ _ (LBH _ HIn)) as (? & ? & ? & ?);
        cbn [ab_addr ab_size] in *; lia).
  pose proof (rng_of_hblk8 AI _ _ _ _ _ _ _ AHz HW' ltac:(lia)) as (RW & RSW).
  clear FRAz R1.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  assert (DB : 4 <= DST /\ DST + dcap < 2^64)
    by (destruct HDST as (pD & AD & ND & HInD & _ & HD1 & HD2); pose proof (ablk_lin _ _ (LBH _ HInD)) as (? & ? & ? & ?);
        cbn [ab_addr ab_size] in *; unfold AIMG_HI in *; lia).
  assert (SB : 0 <= S0 /\ S0 + zlen bs <= ATOP)
    by (destruct SRCH as (pS & AS & NS & HInS & HS1 & HS2); pose proof (ablk_lin _ _ (LBH _ HInS)) as (? & ? & ? & ?);
        cbn [ab_addr ab_size] in *; lia).
  match goal with |- context [Z_to_bv 64 (Z.land (zlen src) ?M - Z.land ncl ?M)] =>
    replace (Z_to_bv 64 (Z.land (zlen src) M - Z.land ncl M)) with (Z_to_bv 64 (zlen bs))
      by (f_equal; change M with (Z.ones 64); rewrite !Z.land_ones by lia; rewrite !Z.mod_small by lia; lia) end.
  zstep. bcase K0.
  - zstep. bcase K1; [| fdw_kc K1].
    zstep. zstep. bcase K2; [| fdw_kc K2].
    zstep. zstep. zstep. zstep. bcase K3; [| fdw_kc K3].
    assert (E0 : dt_fastMode d = 0) by (destruct CF as [E|E]; [exact E| rewrite E in K0; vm_compute in K0; discriminate K0]).
    rewrite E0 in DEQ, DOK, DTH.
    eapply (fdw_call _ 0 false mz j0' j32 j48 d S0 bs jd);
      first [exact SAFE| exact E0| reflexivity| exact FI| exact DEQ| exact TL| exact CL| exact CO| exact DTH| exact DTC| exact HW| exact W8
            | exact WKD| exact SRC| exact SRCF| exact SRCL| exact S16| exact SRCH| exact JD| exact JDL| exact D1| exact D2| exact D3
            | exact ZF| exact SC| exact ZK| exact DOK].
  - zstep. bcase K1; [| fdw_kc K1].
    zstep. zstep. bcase K2; [| fdw_kc K2].
    zstep. zstep. zstep. zstep. bcase K3; [| fdw_kc K3].
    assert (E0 : dt_fastMode d = 1) by (destruct CF as [E|E]; [exfalso; apply K0; rewrite E; vm_compute; reflexivity| exact E]).
    rewrite E0 in DEQ, DOK, DTH.
    eapply (fdw_call _ 1 true mz j0' j32 j48 d S0 bs jd);
      first [exact FAST| exact E0| reflexivity| exact FI| exact DEQ| exact TL| exact CL| exact CO| exact DTH| exact DTC| exact HW| exact W8
            | exact WKD| exact SRC| exact SRCF| exact SRCL| exact S16| exact SRCH| exact JD| exact JDL| exact D1| exact D2| exact D3
            | exact ZF| exact SC| exact ZK| exact DOK].
Qed.

  (* [comment removed for export] *)
  Lemma fdw_bd_ret : forall mx m5 j0' j32 j48 (d : dtable) msv tl ncl (jd : list byte)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    finv mx j0' j32 j48 -> rw_cells bsegs mx (SPAf SPV + 24) [C8 (Z_to_bv 64 ncl)] ->
    AHEAP AI L RNG st (FB0 FF :: LB) m5 -> mem_inv bsegs m5 -> stk bsegs m5 lo (SPAf SPV) ->
    magree bsegs (fun a => aclient_addr CI (FB0 FF :: LB) (SPAf SPV) a /\ ~ (W + 512 <= a < W + 512 + FSE_DTABLE_SIZE tl)
                           /\ ~ (W + 512 + FSE_DTABLE_SIZE tl <= a < W + 512 + FSE_DTABLE_SIZE tl + FSE_BUILD_DTABLE_WKSP_SIZE tl msv))
           mx m5 ->
    u8arr bsegs m5 (W + 512) (fse_dt_bytes d) ->
    fse_decompress_wksp (repeat 0 256) dcap src maxLog wks
      = decompress_usingDTable (skipn (Z.to_nat ncl) src) d dcap (negb (dt_fastMode d =? 0)) ->
    dtable_ok msv tl d -> 0 <= msv <= 255 -> 5 <= tl <= 12 ->
    hblk8 LB W wks -> W mod 8 = 0 -> 512 <= wks -> FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= wks - 512 - FSE_DTABLE_SIZE tl ->
    bytes_at bsegs mx S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src -> zlen src <= 65536 ->
    bufH LB S (zlen src) -> 16 <= S -> 1 <= ncl <= zlen src ->
    u8arr bsegs mx DST jd -> zlen jd = dcap ->
    (DST + dcap <= S \/ S + zlen src <= DST) -> (DST + dcap <= W \/ W + wks <= DST) -> (S + zlen src <= W \/ W + wks <= S) ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 0x9846c) (Z_to_bv 64 (SPAf SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV))
               (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF)
               (Z_to_bv 64 (W + 512)) (Z_to_bv 64 dcap) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 W) (Z_to_bv 64 wks) (Z_to_bv 64 S)
               (Z_to_bv 64 (S + ncl)) (Z_to_bv 64 (FF + 48)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x9846c) fc None m5 (seg_rom bsegs)).
Proof.
  intros mx m5 j0' j32 j48 d msv tl ncl jd x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    FI C24 AH5 MI5 STL5 MG5 DTB DEQ DOK MSV TL HW W8 WK5 WKB SRC SRCB SRCL SRCH S16 NCL JD JDL DD1 DD2 DD3.
  pose proof atop_range as ATR. unfold AFSE_DECOMP_STACK in LO.
  pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
  assert (HW' : hblk8 (FB0 FF :: LB) W wks)
    by (destruct HW as (p & A0 & N0 & HIn & HN & HA & HB); exists p, A0, N0; split; [right; exact HIn| lia]).
  pose proof (zshadow_of_hblk8 AI _ _ _ _ _ _ _ AH5 HW' ltac:(lia)) as ZW.
  pose proof (rng_of_hblk8 AI _ _ _ _ _ _ _ AH5 HW' ltac:(lia)) as (RW & RSW).
  pose proof FI as (_ & _ & _ & _ & _ & _ & _ & FRAx & _).
  assert (WB : 0 <= W /\ W + wks <= ATOP)
    by (destruct HW as (p & A0 & N0 & HIn & _ & HA & HB); pose proof (ablk_lin _ _ (LBH _ HIn)) as (? & ? & ? & ?);
        cbn [ab_addr ab_size] in *; lia).
  assert (SZ : 0 <= FSE_DTABLE_SIZE tl /\ 0 <= FSE_BUILD_DTABLE_WKSP_SIZE tl msv)
    by (unfold FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE; pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia).
  pose proof (AI_layout AI _ _ _ _ _ AH5) as (LY1 & LY2 & LY3 & _).
  assert (FRA5 : rw_cells bsegs m5 (SPAf SPV) [CB 32 j0'; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST);
                                     C8 (Z_to_bv 64 2147450880); CB 8 j32; C8 (Z_to_bv 64 FF); CB 72 j48])
    by (eapply rw_cells_magree; [exact MG5| exact FRAx|]; intros a Ha; cbn in Ha; split; [left; lia| split; lia]).
  assert (WK6 : 520 <= wks) by (unfold FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE in WKB; pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia).
  zstep. replace (Z_to_bv 64 (-120)) with (Z_to_bv 64 (2^64 - 120)) by (apply Z_to_bv_eqm; reflexivity).
  zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
  zstep. zstep. zstep. zstep.
  pose proof (chkZ m5 W wks (W + 514) ZW ltac:(lia) ltac:(lia)) as RDB.
  zstep. rewrite ?sxb0. clear RDB.
  zstep. replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by (vm_compute; reflexivity). cbv iota.
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (dtok_cellsA _ _ _ DOK ltac:(lia)) as (CO & CL & CT & CF).
  assert (ZD : zlen (skipn (Z.to_nat ncl) src) = zlen src - ncl) by (rewrite length_skipn; lia).
  pose proof HW as (p & A0 & N0 & HIn & HN & HA & HB). pose proof (FFD _ HIn) as FFW. cbn [ab_addr ab_size] in FFW.
  pose proof (ablk_lin _ _ FH) as FHL.
  pose proof FI as (_ & MGx & _).
  pose proof (rclean_shclean _ _ RCL) as SHC. pose proof (shclean_hull _ _ _ _ _ SHC) as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6).
  unfold KEND in HU6.
  assert (ABM : 0 <= ABIT_MASK /\ ABIT_MASK + 128 <= 2^47) by (unfold ABIT_MASK; lia).
  assert (SG0 : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a') -> 0 <= a' < 2^47 -> PAGf LB SPV DST dcap W wks (shad a')).
  { intros a' H1 H2. unfold AF_huf_fdw_top1.PAGf. split; [apply cl_shadow; destruct H1 as [H1|H1]; [left; exact H1| right; left; exact H1]|].
    split; [eapply (sh_hblk_out _ _ _ _ _ _ HDST LBH); lia| eapply (sh_hblk_out _ _ _ _ _ _ HW LBH); lia]. }
  assert (SG1 : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake (FB0 FF :: LB) a') -> 0 <= a' < 2^47 ->
      aclient_addr CI (FB0 FF :: LB) (SPAf SPV) (shad a') /\ ~ (W + 512 <= shad a' < W + 512 + FSE_DTABLE_SIZE tl)
      /\ ~ (W + 512 + FSE_DTABLE_SIZE tl <= shad a' < W + 512 + FSE_DTABLE_SIZE tl + FSE_BUILD_DTABLE_WKSP_SIZE tl msv)).
  { intros a' H1 H2. split; [apply cl_shadow; exact H1|].
    split; [eapply (sh_hblk_out _ _ _ _ _ _ HW LBH); lia| eapply (sh_hblk_out _ _ _ _ _ _ HW LBH); lia]. }
  assert (FI5 : finv m5 j0' j32 j48).
  { eapply (finv_transport mx m5 j0' j32 j48 _ FI AH5 MI5 STL5 MG5).
    - intros a Ha. destruct (pag_rd LB FF SPV (SPAf SPV) DST dcap W wks wks a HCI HCI0 FH ltac:(lia) ltac:(lia) ltac:(lia) LBH FFD Ha)
        as (H1 & H2 & _). split; [exact H1| split; lia].
    - intros a Ha. split; [left; lia| split; lia].
    - intros a Ha. split; [right; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]| split; lia].
    - intros a Ha. pose proof (ffsh_pre FF a F64 ltac:(lia) Ha) as Ha'.
      replace a with (shad (8 * (a - ASHOFF))) by apply shad_inv8.
      apply SG1; [right; right; unfold in_fake; exists 0, FF, 64; split; [left; reflexivity| lia]| lia]. }
  assert (C245 : rw_cells bsegs m5 (SPAf SPV + 24) [C8 (Z_to_bv 64 ncl)])
    by (eapply rw_cells_magree; [exact MG5| exact C24|]; intros a Ha; cbn in Ha; split; [left; lia| split; lia]).
  assert (DTB2 : rw_cells bsegs m5 (W + 512) [C2 (Z_to_bv 64 tl); C2 (Z_to_bv 64 (dt_fastMode d))] /\
                 bytes_at bsegs m5 (W + 512 + 4) (concat (map fse_cell_bytes (dt_cells d)))).
  { pose proof DTB as DT0. unfold fse_dt_bytes in DT0. rewrite CT, app_assoc in DT0.
    apply RF_huf_bdt_model.u8arr_app in DT0 as (DT1 & DT2). split.
    - eapply rw_cells_recast; [exact (rw_cells_of_u8arr _ _ _ _ DT1)| cbn; tauto| cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity|
        cbn [cells_size csize]; rewrite length_app, !length_le2; reflexivity].
    - rewrite length_app, !length_le2 in DT2. destruct DT2 as (DT2 & _). exact DT2. }
  assert (SRC5 : bytes_at bsegs m5 (S + ncl) (map (Z_to_bv 8) (skipn (Z.to_nat ncl) src))).
  { pose proof SRCH as (pS & AS & NS & HInS & HS1 & HS2).
    assert (SRCm : bytes_at bsegs m5 S (map (Z_to_bv 8) src)).
    { eapply bytes_at_magree; [exact MG5| exact SRC|]. intros a Ha. rewrite length_map in Ha.
      split; [right; right; left; exists (mkABlock (ABHeap pS) AS NS); split; [right; exact HInS| cbn; lia]| split; lia]. }
    rewrite <- (firstn_skipn (Z.to_nat ncl) src), map_app in SRCm. apply bytes_at_app in SRCm as (_ & SRCm).
    assert (E : Z.of_nat (length (firstn (Z.to_nat ncl) src)) = ncl) by (rewrite length_firstn, Nat.min_l by lia; lia).
    rewrite length_map, E in SRCm. exact SRCm. }
  assert (SRCF : Forall (fun c => 0 <= c < 256) (skipn (Z.to_nat ncl) src))
    by exact (all_bytes_Forall _ (all_bytes_skipn _ _ (Forall_all_bytes _ SRCB))).
  assert (SRCHd : bufH LB (S + ncl) (zlen src - ncl))
    by (destruct SRCH as (pS & AS & NS & HInS & HS1 & HS2); exists pS, AS, NS; split; [exact HInS| lia]).
  assert (JD5 : u8arr bsegs m5 DST jd).
  { destruct JD as (JD1 & JD2). pose proof HDST as (pD & AD & ND & HInD & _ & HD1 & HD2).
    assert (HPD : forall a, DST <= a < DST + dcap -> aclient_addr CI (FB0 FF :: LB) (SPAf SPV) a /\ ~ (W + 512 <= a < W + 512 + FSE_DTABLE_SIZE tl)
      /\ ~ (W + 512 + FSE_DTABLE_SIZE tl <= a < W + 512 + FSE_DTABLE_SIZE tl + FSE_BUILD_DTABLE_WKSP_SIZE tl msv)).
    { intros a Ha. split; [right; right; left; exists (mkABlock (ABHeap pD) AD ND); split; [right; exact HInD| cbn; lia]| split; lia]. }
    split; [eapply bytes_at_magree; [exact MG5| exact JD1| intros a Ha; apply HPD; lia]|
            eapply wr_at_magree; [exact MG5| exact JD2| intros a Ha; apply HPD; lia]]. }
  assert (ZF5 : zshadow m5 (SPAf SPV + 80) 72).
  { assert (Z0 : zshadow m (SPAf SPV + 80) 72).
    { apply zshadow_of_unpoisoned8; [| lia| lia| lia]. eapply shclean_unpoisoned. eapply shclean_sub; [exact SHC| lia| lia| lia]. }
    assert (Z1 : zshadow mx (SPAf SPV + 80) 72)
      by (eapply zshadow_magree; [exact Z0| exact MGx| intros a Ha; apply SG0; [left; lia| lia]| lia| lia]).
    eapply zshadow_magree; [exact Z1| exact MG5| intros a Ha; apply SG1; [left; lia| lia]| lia| lia]. }
  assert (ZK5 : zshadow m5 ABIT_MASK 128).
  { assert (Z1 : zshadow mx ABIT_MASK 128)
      by (eapply zshadow_magree; [exact ZMK| exact MGx| intros a Ha; apply SG0; [right; exact (MKCI a Ha)| lia]| lia| lia]).
    eapply zshadow_magree; [exact Z1| exact MG5| intros a Ha; apply SG1; [right; left; exact (MKCI a Ha)| lia]| lia| lia]. }
  assert (SC5 : shclean m5 (SPAf SPV + 112) (SPAf SPV + 152) (r_rlo rstk) (r_rhi rstk)).
  { assert (SC0 : shclean m (SPAf SPV + 112) (SPAf SPV + 152) (r_rlo rstk) (r_rhi rstk)) by (eapply shclean_sub; [exact SHC| lia| lia| lia]).
    assert (SH0 : forall s, shad (r_rlo rstk) <= s < shad (r_rhi rstk) -> exists a', s = shad a' /\ ATOP <= a' < 2^47).
    { intros s Hs. exists (8 * (s - ASHOFF)). split; [symmetry; apply shad_inv8|].
      pose proof (shrange_pre _ _ s Hs ltac:(lia)). lia. }
    assert (SC1 : shclean mx (SPAf SPV + 112) (SPAf SPV + 152) (r_rlo rstk) (r_rhi rstk))
      by (eapply shclean_magree; [exact SC0| exact MGx| intros s Hs; destruct (SH0 s Hs) as (a' & -> & Ha'); apply SG0; [left; lia| lia]| lia]).
    eapply shclean_magree; [exact SC1| exact MG5| intros s Hs; destruct (SH0 s Hs) as (a' & -> & Ha'); apply SG1; [left; lia| lia]| lia]. }
  assert (DOKr : dres_ok (decompress_usingDTable (skipn (Z.to_nat ncl) src) d dcap (negb (dt_fastMode d =? 0)))).
  { destruct (decompress_usingDTable_safe (skipn (Z.to_nat ncl) src) d msv tl dcap (negb (dt_fastMode d =? 0))
        (all_bytes_skipn _ _ (Forall_all_bytes _ SRCB)) DOK ltac:(lia)
        ltac:(intros Hf; destruct CF as [E|E]; [rewrite E in Hf; cbn in Hf; discriminate Hf| exact E]) ltac:(lia))
      as [(l & E & _)|(e & E)]; rewrite E; exact I. }
  assert (WKD : 512 + 4 + 4 * 2^tl <= wks) by (unfold FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE in WKB; lia).
  eapply (fdw_dec m5 j0' j32 j48 d (S + ncl) ncl (skipn (Z.to_nat ncl) src) jd).
  all: try rewrite CT.
  all: try rewrite ZD.
  all: try first [exact DEQ| exact HW| exact W8| exact JDL| exact FI5| exact C245| exact (proj1 DTB2)| exact (proj2 DTB2)| exact SRC5| exact SRCF|
                  exact SRCHd| exact JD5| exact ZF5| exact SC5| exact ZK5| exact DOKr| exact WKD| exact CO| exact CL| exact CF| reflexivity| lia].
Qed.

  Lemma fdw_rd_428 : forall mx j0' j32 j48 (rt : list Z) msv tl ncl (jd jwr : list byte)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    finv mx j0' j32 j48 -> rw_cells bsegs mx (SPAf SPV + 24) [C8 (Z_to_bv 64 ncl)] ->
    read_ncount (repeat 0 256) 255 src = Ok (rt, msv, tl, ncl) ->
    u8arr bsegs mx W (u16s (map (Z_to_bv 64) rt)) ->
    rw_cells bsegs mx (FF + 48) [C4 (Z_to_bv 64 msv)] -> rw_cells bsegs mx (FF + 32) [C4 (Z_to_bv 64 tl)] ->
    u8arr bsegs mx (W + 512) jwr -> zlen jwr = wks - 512 ->
    u8arr bsegs mx DST jd -> zlen jd = dcap ->
    bytes_at bsegs mx S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    hblk8 LB W wks -> W mod 8 = 0 -> bufH LB S (zlen src) -> 16 <= S ->
    512 <= wks -> wks < 2^32 -> 0 <= maxLog <= 12 -> zlen src <= 65536 ->
    (DST + dcap <= S \/ S + zlen src <= DST) -> (DST + dcap <= W \/ W + wks <= DST) -> (S + zlen src <= W \/ W + wks <= S) ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 0x98300) (Z_to_bv 64 (SPAf SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV))
               (Z_to_bv 64 ncl) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (FF + 32))
               (Z_to_bv 64 (W + 512)) (Z_to_bv 64 dcap) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 W) (Z_to_bv 64 wks) (Z_to_bv 64 S)
               (Z_to_bv 64 maxLog) (Z_to_bv 64 (FF + 48)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x9830c) fc None mx (seg_rom bsegs)).
Proof.
  intros mx j0' j32 j48 rt msv tl ncl jd jwr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    FI C24 RD RTW MSC TLC JW JWL JD JDL SRC SRCB HW W8 SRCH S16 WK5 WK32 ML SRCL DD1 DD2 DD3.
  pose proof atop_range as ATR. unfold AFSE_DECOMP_STACK in LO.
  pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
  destruct (read_ncount_total (repeat 0 256) 255 src (Forall_all_bytes _ SRCB) ltac:(lia) ltac:(vm_compute; intros Hc; discriminate Hc))
    as [(nc & ms & tg & n & E & LN & MS & TG & NN & ZR & ZR2 & WS)|(e & E)]; rewrite RD in E; [|discriminate E].
  injection E as E1 E2 E3 E4. subst nc ms tg n. clear ZR2.
  assert (NN' : 1 <= ncl <= zlen src) by (unfold FseNCount.Zlength in NN; lia). clear NN.
  pose proof FI as (AHx & MGx & MIx & SHx & F0x & F56x & FRBx & FRAx & STLx & STGx).
  pose proof (AI_layout AI _ _ _ _ _ AHx) as (LY1 & LY2 & LY3 & _).
  pose proof (ablk_lin _ _ FH) as FHL.
  assert (WB : 0 <= W /\ W + wks <= ATOP)
    by (destruct HW as (p & A0 & N0 & HIn & _ & HA & HB); pose proof (ablk_lin _ _ (LBH _ HIn)) as (? & ? & ? & ?);
        cbn [ab_addr ab_size] in *; lia).
  assert (SB : 0 <= S /\ S + zlen src <= ATOP)
    by (destruct SRCH as (pS & AS & NS & HInS & HS1 & HS2); pose proof (ablk_lin _ _ (LBH _ HInS)) as (? & ? & ? & ?);
        cbn [ab_addr ab_size] in *; lia).
  pose proof (proj1 (ABytes.rw_cells_app _ _ _ [CB 32 j0'] _) FRAx) as (_ & R1).
  pose proof (proj1 (ABytes.rw_cells_app _ _ _ [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] _) R1) as (P32 & _).
  apply (rw_cells_eqA _ _ (SPAf SPV + 32)) in P32; [|reflexivity].
  clear R1 FRAx.
  zstep.
  rewrite ?(sx32_small tl) by lia.
  zstep. replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 (2^64 - 44)) by (apply Z_to_bv_eqm; reflexivity).
  zstep. bcase K0.
  2: { assert (DR : dresA DST dcap (fse_decompress_wksp (repeat 0 256) dcap src maxLog wks) mx (2^64 - 44)).
         { unfold fse_decompress_wksp. replace (wks <? 512) with false by (symmetry; apply Z.ltb_ge; lia). unfold FSE_MAX_SYMBOL_VALUE. rewrite RD. cbn [FseNCount.bind].
           replace (maxLog <? tl) with true by (symmetry; apply Z.ltb_lt; lia). cbn.
           split; [| split]; try unfold ZSTD_error_tableLog_tooLarge; lia. }
       eapply (fdw_exit mx j0' j32 j48 (2^64 - 44)); [exact FI| exact DR| lia]. }
  do 5 zstep. bcase K1; [| revert K1; clear - NN' SB ATR S16 TG; intros K1; fdw_kc K1].
  do 4 zstep. bcase K2; [| revert K2; clear - NN' SB ATR S16 TG; intros K2; fdw_kc K2].
  do 2 zstep. bcase K3; [| revert K3; clear - NN' SB ATR S16 TG; intros K3; fdw_kc K3].
  do 16 zstep. bcase K4.
  all: rewrite (sx32_small msv) in K4 |- * by lia.
  all: match type of K4 with context [?E mod 2^64] => lazymatch E with Z.land _ _ + 516 =>
         assert (EW : E mod 2^64 = FSE_DECOMPRESS_WKSP_SIZE tl msv) end end.
  1,3: clear - rc K0 ML MS TG; assert (TL : 5 <= tl <= 12) by lia; clear K0 ML TG;
    rewrite (sllw_pow2 tl) by lia;
    assert (TP : 32 <= 2^tl <= 4096) by (split; [change 32 with (2^5)| change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia);
    rewrite unsigned_lit by lia;
    rewrite (Z.mod_small (2^tl)) by lia; rewrite (Z.mod_small (msv + 1)) by lia;
    rewrite zext32_sh31 by lia;
    replace (Z.land tl 63) with tl by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia);
    rewrite !Z.shiftl_mul_pow2 by lia; change (2^2) with 4;
    rewrite (Z.mod_small (2^tl * 4 + 1 * 2^tl + 2 * (msv + 1) + 19)) by lia;
    match goal with |- (Z.land ?X ?M + 516) mod _ = _ => replace M with (2^63 - 4) by (vm_compute; reflexivity) end;
    rewrite land_m63 by lia;
    rewrite Z.mod_small by (pose proof (Z.mod_pos_bound (2^tl * 4 + 1 * 2^tl + 2 * (msv + 1) + 19) 4 ltac:(lia)); lia);
    apply wksp_norm; [lia| lia| reflexivity].
  all: rewrite EW in K4.
  { assert (DR : dresA DST dcap (fse_decompress_wksp (repeat 0 256) dcap src maxLog wks) mx (2^64 - 44)).
    { unfold fse_decompress_wksp, FSE_MAX_SYMBOL_VALUE; replace (wks <? 512) with false by (symmetry; apply Z.ltb_ge; lia);
      rewrite RD; cbn [FseNCount.bind];
      replace (maxLog <? tl) with false by (symmetry; apply Z.ltb_ge; lia);
      replace (wks <? FSE_DECOMPRESS_WKSP_SIZE tl msv) with true by (symmetry; apply Z.ltb_lt; exact K4); cbn;
      split; [| split]; try unfold ZSTD_error_tableLog_tooLarge; lia. }
    eapply (fdw_exit0 mx j0' j32 j48 (2^64 - 44)); [exact FI| exact DR| lia]. }
  assert (TP : 32 <= 2^tl <= 4096) by (split; [change 32 with (2^5)| change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
  rewrite ?(sllw_pow2 tl) by lia. rewrite ?(Z.mod_small (2^tl)) by lia.
  do 2 zstep.
  rewrite (zb_lxor_ones (W + 512)) by lia.
  match goal with |- context [Z.land (2^tl) ?M] =>
    replace (Z.land (2^tl) M) with (2^tl)
      by (replace M with (Z.ones 64) by (vm_compute; reflexivity); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia) end.
  rewrite ?Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
  zstep. bcase K5.
  2: { revert K5; clear - WB WK5 TP ATR; intros K5; exfalso; lia. }
  do 6 zstep.
  assert (TL12 : 5 <= tl <= 12) by (clear - K0 ML TG; lia).
  destruct (WS ltac:(lia)) as (WL & WSm).
  assert (LRT : length rt = 256%nat) by (rewrite LN; apply repeat_length).
  assert (HOK : ncount_ok rt msv tl).
  { unfold ncount_ok, HufPure_FseDecompRT.ncl. rewrite HufPure_FseReadBridge.wsum_eq.
    refine (conj _ (conj _ (conj _ (conj WL WSm)))).
    - unfold FSE_MAX_SYMBOL_VALUE. clear - MS. lia.
    - unfold FSE_MIN_TABLELOG, FSE_TABLELOG_ABSOLUTE_MAX. clear - TL12. lia.
    - unfold FseNCount.Zlength. rewrite LRT. clear - MS. lia. }
  assert (WKB : FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= wks - 512 - FSE_DTABLE_SIZE tl).
  { revert K4. clear - TL12 MS TP. intros K4.
    unfold FSE_DECOMPRESS_WKSP_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE, FSE_DTABLE_SIZE, FSE_MAX_SYMBOL_VALUE in *.
    Z.div_mod_to_equations. lia. }
  assert (SZ : 0 <= FSE_DTABLE_SIZE tl /\ 0 <= FSE_BUILD_DTABLE_WKSP_SIZE tl msv)
    by (unfold FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE; clear - TP MS; lia).
  destruct (build_dtable_ok rt msv tl HOK (wks - 512 - FSE_DTABLE_SIZE tl) ltac:(unfold FSE_MAX_TABLELOG; clear - TL12; lia) WKB)
    as (d & BD & DOK).
  pose proof (rt_bounds rt msv tl LRT MS ltac:(clear - TL12; lia) WL WSm ZR) as RTB.
  destruct (u8arr_sub2 mx (W + 512) jwr (Z.to_nat (FSE_DTABLE_SIZE tl)) (Z.to_nat (FSE_BUILD_DTABLE_WKSP_SIZE tl msv))) as (JDT & JWK).
  { revert JWL WKB SZ. clear - TL12 MS TP. intros. lia. }
  { exact JW. }
  rewrite Z2Nat.id in JWK by (clear - SZ; lia).
  assert (BDT1 : W <= W + 512 /\ W + 512 + FSE_DTABLE_SIZE tl <= W + wks) by (clear - WKB SZ; lia).
  assert (BWK1 : W <= W + 512 + FSE_DTABLE_SIZE tl /\ W + 512 + FSE_DTABLE_SIZE tl + FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= W + wks)
    by (clear - WKB SZ; lia).
  assert (BNC1 : W + 2 * zlen rt <= W + wks /\ W + 2 * zlen rt <= W + 512) by (rewrite LRT; clear - WK5; lia).
  assert (BNC2 : W + 2 * zlen rt <= W + 512 + FSE_DTABLE_SIZE tl) by (clear - BNC1 SZ; lia).
  assert (LJ1 : zlen (firstn (Z.to_nat (FSE_DTABLE_SIZE tl)) jwr) = FSE_DTABLE_SIZE tl)
    by (rewrite length_firstn; clear - JWL WKB SZ; lia).
  assert (LJ2 : zlen (firstn (Z.to_nat (FSE_BUILD_DTABLE_WKSP_SIZE tl msv)) (skipn (Z.to_nat (FSE_DTABLE_SIZE tl)) jwr))
                = FSE_BUILD_DTABLE_WKSP_SIZE tl msv)
    by (rewrite length_firstn, length_skipn; clear - JWL WKB SZ; lia).
  assert (WMD : (W + 512) mod 4 = 0 /\ (W + 512 + FSE_DTABLE_SIZE tl) mod 2 = 0 /\ W mod 2 = 0)
    by (unfold FSE_DTABLE_SIZE; clear - W8; Z.div_mod_to_equations; lia).
  assert (WKR : 0 <= wks - 512 - FSE_DTABLE_SIZE tl < 2^64) by (clear - WKB SZ WK32; lia).
  assert (STB : lo <= SPAf SPV - AFSE_BUILD_STACK /\ SPAf SPV + 16 < al_top L /\ SPAf SPV mod 16 = 0)
    by (unfold AFSE_BUILD_STACK; clear - LO SPAB SPT SPA32; Z.div_mod_to_equations; lia).
  assert (LBH' : forall b, In b (FB0 FF :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b))
    by (intros b [<-|Hb]; [exact FH| exact (LBH b Hb)]).
  assert (NCB : Forall (fun c => - 32768 <= c < 32768) rt)
    by (eapply Forall_impl; [|exact RTB]; intros c Hc; cbv beta in *; clear - Hc; lia).
  replace (Z_to_bv 64 (W + 512 + (2 ^ tl * 4 + 4))) with (Z_to_bv 64 (W + 512 + FSE_DTABLE_SIZE tl)) by (f_equal; unfold FSE_DTABLE_SIZE; ring).
  replace (Z_to_bv 64 (wks - (2 ^ tl * 4 + 4) + -512)) with (Z_to_bv 64 (wks - 512 - FSE_DTABLE_SIZE tl)) by (f_equal; unfold FSE_DTABLE_SIZE; ring).
  replace (Z_to_bv 64 (ncl + S)) with (Z_to_bv 64 (S + ncl)) by (f_equal; ring).
  eapply evtF_cut.
  { pose proof BDT as BD0. unfold fse_build_stmtA in BD0.
    eapply BD0 with (m := mx) (LB := FB0 FF :: LB) (SPV := SPAf SPV) (DT := W + 512) (NC := W) (WK := W + 512 + FSE_DTABLE_SIZE tl)
      (wks := wks - 512 - FSE_DTABLE_SIZE tl) (msv := msv) (tl := tl) (nc := rt) (d := d) (lo := lo)
      (jdt := firstn (Z.to_nat (FSE_DTABLE_SIZE tl)) jwr)
      (jw := firstn (Z.to_nat (FSE_BUILD_DTABLE_WKSP_SIZE tl msv)) (skipn (Z.to_nat (FSE_DTABLE_SIZE tl)) jwr)); clear BD0.
    all: first [exact BD| exact (proj1 MS)| exact WKR| exact AHx| exact LBH'| exact JDT| exact JWK| exact (proj1 RTW)
               | exact MIx| exact STLx| exact BOT| exact (proj1 STB)| exact (proj1 (proj2 STB))| exact (proj2 (proj2 STB))| exact RSTK| exact RI
               | exact (proj1 WMD)| exact (proj1 (proj2 WMD))| exact (proj2 (proj2 WMD))| exact LJ1| exact LJ2
               | exact (hblk8_sub _ _ _ _ _ _ HW (proj1 BDT1) (proj2 BDT1))
               | exact (hblk8_sub _ _ _ _ _ _ HW (proj1 BWK1) (proj2 BWK1))
               | exact (hblk8_sub _ _ _ _ _ _ HW (Z.le_refl W) (proj1 BNC1))
               | left; apply Z.le_refl| right; exact (proj2 BNC1)| right; exact BNC2
               | eapply Forall_impl; [|exact RTB]; intros c Hc; cbv beta in *; clear - Hc; lia]. }
  cbv beta. intros ms' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m5 & -> & MI5 & STK5 & MG5 & AH5 & DT5).
  rd_retlit.
  assert (DEQ : fse_decompress_wksp (repeat 0 256) dcap src maxLog wks
                = decompress_usingDTable (skipn (Z.to_nat ncl) src) d dcap (negb (dt_fastMode d =? 0))).
  { unfold fse_decompress_wksp, FSE_MAX_SYMBOL_VALUE. replace (wks <? 512) with false by (symmetry; apply Z.ltb_ge; clear - WK5; lia).
    rewrite RD. cbn [FseNCount.bind].
    replace (maxLog <? tl) with false by (symmetry; apply Z.ltb_ge; clear - K0; lia).
    replace (wks <? FSE_DECOMPRESS_WKSP_SIZE tl msv) with false by (symmetry; apply Z.ltb_ge; revert K4; clear; intros; lia).
    rewrite (proj2 (Z.leb_le 0 ncl)) by (clear - NN'; lia).
    rewrite (proj2 (Z.leb_le ncl _)) by (unfold FseNCount.Zlength; clear - NN'; lia).
    cbn [andb FseNCount.bind FseNCount.assert]. rewrite BD. cbn [FseNCount.bind]. reflexivity. }
  eapply (fdw_bd_ret mx m5 j0' j32 j48 d msv tl ncl jd);
    first [exact FI| exact C24| exact AH5| exact MI5| exact STK5| exact MG5| exact DT5| exact DEQ| exact DOK| exact MS| exact TL12
          | exact HW| exact W8| exact WK5| exact WKB| exact SRC| exact SRCB| exact SRCL| exact SRCH| exact S16| exact NN'| exact JD
          | exact JDL| exact DD1| exact DD2| exact DD3].
Qed.

  (* [comment removed for export] *)
  Lemma fdw_rd_ok : forall mx j0' j32 j48 (rt : list Z) msv tl ncl (jd jwr : list byte)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    finv mx j0' j32 j48 ->
    read_ncount (repeat 0 256) 255 src = Ok (rt, msv, tl, ncl) ->
    u8arr bsegs mx W (u16s (map (Z_to_bv 64) rt)) ->
    rw_cells bsegs mx (FF + 48) [C4 (Z_to_bv 64 msv)] -> rw_cells bsegs mx (FF + 32) [C4 (Z_to_bv 64 tl)] ->
    u8arr bsegs mx (W + 512) jwr -> zlen jwr = wks - 512 ->
    u8arr bsegs mx DST jd -> zlen jd = dcap ->
    bytes_at bsegs mx S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    hblk8 LB W wks -> W mod 8 = 0 -> bufH LB S (zlen src) -> 16 <= S ->
    512 <= wks -> wks < 2^32 -> 0 <= maxLog <= 12 -> zlen src <= 65536 ->
    (DST + dcap <= S \/ S + zlen src <= DST) -> (DST + dcap <= W \/ W + wks <= DST) -> (S + zlen src <= W \/ W + wks <= S) ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 0x98300) (Z_to_bv 64 (SPAf SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV))
               (Z_to_bv 64 ncl) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (FF + 32))
               (Z_to_bv 64 (W + 512)) (Z_to_bv 64 dcap) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 W) (Z_to_bv 64 wks) (Z_to_bv 64 S)
               (Z_to_bv 64 maxLog) (Z_to_bv 64 (FF + 48)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x98300) fc None mx (seg_rom bsegs)).
Proof.
  intros mx j0' j32 j48 rt msv tl ncl jd jwr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    FI RD RTW MSC TLC JW JWL JD JDL SRC SRCB HW W8 SRCH S16 WK5 WK32 ML SRCL DD1 DD2 DD3.
  pose proof atop_range as ATR. unfold AFSE_DECOMP_STACK in LO.
  pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
  destruct (read_ncount_total (repeat 0 256) 255 src (Forall_all_bytes _ SRCB) ltac:(lia) ltac:(vm_compute; intros Hc; discriminate Hc))
    as [(nc & ms & tg & n & E & LN & MS & TG & NN & ZR & ZR2 & WS)|(e & E)]; rewrite RD in E; [|discriminate E].
  injection E as E1 E2 E3 E4. subst nc ms tg n. clear ZR ZR2 WS.
  assert (NN' : 1 <= ncl <= zlen src) by (unfold FseNCount.Zlength in NN; lia). clear NN.
  pose proof FI as (AHx & MGx & MIx & SHx & F0x & F56x & FRBx & FRAx & STLx & STGx).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (AI_layout AI _ _ _ _ _ AHx) as (LY1 & LY2 & LY3 & _).
  pose proof (ablk_lin _ _ FH) as FHL.
  assert (WB : 0 <= W /\ W + wks <= ATOP)
    by (destruct HW as (p & A0 & N0 & HIn & _ & HA & HB); pose proof (ablk_lin _ _ (LBH _ HIn)) as (? & ? & ? & ?);
        cbn [ab_addr ab_size] in *; lia).
  assert (DB : 0 <= DST /\ DST + dcap <= ATOP)
    by (destruct HDST as (pD & AD & ND & HInD & _ & HD1 & HD2); pose proof (ablk_lin _ _ (LBH _ HInD)) as (? & ? & ? & ?);
        cbn [ab_addr ab_size] in *; lia).
  assert (SB : 0 <= S /\ S + zlen src <= ATOP)
    by (destruct SRCH as (pS & AS & NS & HInS & HS1 & HS2); pose proof (ablk_lin _ _ (LBH _ HInS)) as (? & ? & ? & ?);
        cbn [ab_addr ab_size] in *; lia).
  assert (HID : hideF (u8arr bsegs mx W (u16s (map (Z_to_bv 64) rt)) /\ u8arr bsegs mx (W + 512) jwr /\ u8arr bsegs mx DST jd
                       /\ bytes_at bsegs mx S (map (Z_to_bv 8) src))) by exact (conj RTW (conj JW (conj JD SRC))).
  zstep. replace (Z_to_bv 64 (-120)) with (Z_to_bv 64 (2^64 - 120)) by (apply Z_to_bv_eqm; reflexivity).
  zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
  pose proof (rw_cells_split_CB bsegs mx (SPAf SPV) [] 32 j0' _ [24; 8]%nat FRAx eq_refl) as FRA1. cbn [app mk_CB_cells] in FRA1.
  pose proof (munch_refl [(SPAf SPV + 24, SPAf SPV + 32)] mx) as MU. pose proof (wmono_refl bsegs mx) as WM.
  zstep.
  pose proof (magree_of_munch bsegs _ _ _ MU WM) as MGm.
  pose proof (proj1 (ABytes.rw_cells_app _ _ _ [CB 24 (take 24 j0')] _) FRA1) as (_ & C24a).
  apply (rw_cells_eqA _ _ (SPAf SPV + 24)) in C24a; [|reflexivity].
  pose proof (proj1 (ABytes.rw_cells_app _ _ _ [C8 (Z_to_bv 64 ncl)] _) C24a) as (C24 & _). clear C24a.
  pose proof (rw_cells_merge bsegs m0 (SPAf SPV) [] [CB 24 (take 24 j0'); C8 (Z_to_bv 64 ncl)] _ FRA1) as FRM.
  cbn [app cells_size csize Nat.add] in FRM.
  assert (FS8 : Z.of_nat (cells_size FDSH) = 8) by reflexivity.
  assert (FI0 : finv m0 (cells_bytes [CB 24 (take 24 j0'); C8 (Z_to_bv 64 ncl)]) j32 j48).
  { refine (conj _ (conj _ (conj MIx (conj _ (conj F0x (conj F56x (conj FRBx (conj FRM (conj STLx STGx))))))))).
    - eapply (AI_frame AI _ _ _ _ mx m0 _ AHx MU WM).
      apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]. left. left. split; lia.
    - eapply magree_munch_step; [exact MGx| exact MU| exact WM|].
      intros a (Ha & HnD & HnW). cbn [outside].
      refine (conj _ I); intros Hr. exact (stack_not_client CI LB SPV lo a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha).
    - pose proof FI as (_ & _ & _ & SHo & _).
      eapply rw_cells_magree; [exact MGm| exact SHo|]. intros a Ha. rewrite FS8 in Ha.
      pose proof (ffsh_pre FF a F64 ltac:(lia) Ha) as Ha'.
      pose proof (shad_lt_atop (8 * (a - ASHOFF)) ltac:(lia)) as Hs. rewrite shad_inv8 in Hs.
      cbn [outside]. refine (conj _ I); intro; lia. }
  unfold hideF in HID. destruct HID as ((RTW1 & RTW2) & (JW1 & JW2) & (JD1 & JD2) & SRCo).
  assert (LRT : Z.of_nat (length (u16s (map (Z_to_bv 64) rt))) = 512)
    by (rewrite u16s_length, length_map, LN, repeat_length; reflexivity).
  assert (RTW0 : u8arr bsegs m0 W (u16s (map (Z_to_bv 64) rt))).
  { split; [eapply bytes_at_magree; [exact MGm| exact RTW1|]| eapply wr_at_magree; [exact MGm| exact RTW2|]];
      intros a Ha; cbn [outside]; refine (conj _ I); intro; lia. }
  assert (JW0 : u8arr bsegs m0 (W + 512) jwr).
  { split; [eapply bytes_at_magree; [exact MGm| exact JW1|]| eapply wr_at_magree; [exact MGm| exact JW2|]];
      intros a Ha; cbn [outside]; refine (conj _ I); intro; lia. }
  assert (JD0 : u8arr bsegs m0 DST jd).
  { split; [eapply bytes_at_magree; [exact MGm| exact JD1|]| eapply wr_at_magree; [exact MGm| exact JD2|]];
      intros a Ha; cbn [outside]; refine (conj _ I); intro; lia. }
  assert (SRC0 : bytes_at bsegs m0 S (map (Z_to_bv 8) src)).
  { eapply bytes_at_magree; [exact MGm| exact SRCo|]. intros a Ha. rewrite length_map in Ha. cbn [outside]. refine (conj _ I); intro; lia. }
  eapply (fdw_rd_428 m0 _ j32 j48 rt msv tl ncl jd jwr);
    first [exact FI0| exact C24| exact RD| exact RTW0| exact MSC| exact TLC| exact JW0| exact JWL| exact JD0| exact JDL| exact SRC0
          | exact SRCB| exact HW| exact W8| exact SRCH| exact S16| exact WK5| exact WK32| exact ML| exact SRCL| exact DD1| exact DD2| exact DD3].
Qed.
End After.

End Asm.
End CANSEC1.
