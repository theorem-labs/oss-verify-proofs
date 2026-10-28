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
     AF_huf_fdw_kit AF_huf_bdt_kit AF_huf_fdw_top1 AF_huf_fdw_top2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require ABytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_fdw_tk RF_huf_bdt_model RF_huf_fdw_sm RF_huf_tbl_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_fdw () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z03K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;Z_to_bv_eqmK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountBZSTD_error_GENERICI47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface9fake0_lekC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface5hblk8C5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface4bufHC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface7zshadowC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeC5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_tbl_iface2@fse_decomp_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1:spaf_propsC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg4SPAfC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeI47Corelib4Init5Logic3and00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgI47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loC47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top19fdw_frameK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg4FRBfC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1;fdhdr_splitC56Stdlib6ZArith6BinInt1Z6shiftrK46Stdlib9micromega7EnvRing3Pol01C5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top14PAGfC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree;magree_monoK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symI5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C47Corelib5Lists7ListDef6repeatC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount;read_ncountC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompHFSE_DECOMPRESS_WKSP_SIZEC56Stdlib6ZArith6BinInt1Z3lebC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp?FSE_DTABLE_SIZEC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dt_fastModeC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompCfse_decompress_wkspC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top15dresAC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top19fdw_closeK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top18fdsh_unpC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm8cl_blockC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm8u8arr_mgC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?bytes_at_magreeC46Stdlib5Lists4List<firstn_skipnC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model9u8arr_appC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_tk:u16_decodeK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib3Tac7sum_natC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_mem@rd_rw_cells_appAC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells7cell_wfC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission5BothW6ABytes<le4_of_bytesC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure?rw_cells_recastK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface<rng_of_hblk8C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5nshadC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow9nshad_divC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface?fse_readk_postAC5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface?fake0_lek_push0C5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface4bufAK47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface6nhullAC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface6shullAC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_subC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface=fse_read_resAC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm9cl_shadowC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface;shad_unshadC5ARocqVerifyHarness?AgentSubmission5BothW5ABase>ablk_disj_bandC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?rw_cells_magreeC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree:stk_magreeC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top16pag_rdC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1=mg_after_callC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_tkAread_ncount_indepC56Stdlib6ZArith6BinInt1Z6ltb_geK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C47Corelib4Init3Nat3subC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith6BinInt1Z8max_specC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top24finvC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top29fdw_rd_okK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top28fdw_exitC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC47Corelib4Init5Logic9False_indK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8evtF_cutC5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top18fdw_openC5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_tbl_iface2@fse_decomp_stmtAC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg5FDHDRC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeK46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompFdecompress_usingDTableC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp<build_dtableC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC47Corelib4Init9Datatypes4andbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount6assertC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC35stdpp4base6lookupC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z3maxC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HII46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg4FDSHI5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6dtable00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxI4ELinuxProcessSemantics5Riscv5Instr5instr00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00I5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_tbl_iface2AAFSE_DECOMP_STACKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_tbl_iface29ABIT_MASKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXI47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1>FDW_OPEN_STACKC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompDFSE_MAX_SYMBOL_VALUEC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountLZSTD_error_tableLog_tooLargeI47Corelib4Init5Logic5False00c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdw8fdw_err1I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_iface@FSE_READ_STACK_AC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSC46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05".
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
Variable kk : nat.
Hypothesis SM0K : stack_malloc_0k_stmt AI fflag rng_fs kk.
(* [comment removed for export] *)
Local Notation PAGf := (AF_huf_fdw_top1.PAGf AI).
Local Notation fdw_open := (AF_huf_fdw_top1.fdw_open AI fflag rng_fs kk SM0K).
Local Notation fdw_close := (AF_huf_fdw_top1.fdw_close AI fflag FFLAG FREL).
Local Notation mg_after_call := (AF_huf_fdw_top1.mg_after_call AI).
Local Notation pag_rd := (AF_huf_fdw_top1.pag_rd AI).
Local Notation fdw_exit := (AF_huf_fdw_top2.fdw_exit AI fflag FFLAG FREL).
Local Notation fdw_rd_ok := (AF_huf_fdw_top2.fdw_rd_ok AI fflag rng_fs FFLAG FREL).

Lemma fdw_err1 : Z_to_bv 64 (-1) = Z_to_bv 64 (2^64 - ZSTD_error_GENERIC).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdw ()) ["CANSEC1"; "Asm"] "p;1p;2p;3p10000p4p7210p1000\p4p710p8g001:j18Tg001Xj10Tg002=j12Tg002[j24Tg0038j23Tg003Uj21Tg0045j27Tg004Oj35Tg004ij36Tg005eR0#8R1%00R2#2%02#0#0#0#0#2'4R2g006J'3R3g007PR4%20,32/12'711121132554e36o"). Qed.

Lemma zp_same : forall n (l l' : list Z), length l = n -> length l' = n -> zero_prefix n l = zero_prefix n l'.
Proof.
  induction n as [|n IH]; intros [|x l] [|y l'] H H'; cbn in *; try discriminate; try reflexivity.
  f_equal. apply IH; lia.
Qed.

Lemma rnc_nc0 : forall (nc0 buf : list Z), length nc0 = 256%nat ->
  read_ncount nc0 255 buf = read_ncount (repeat 0 256) 255 buf.
Proof.
  intros nc0 buf HL.
  assert (HB : forall b, read_ncount_body8 b (255 + 1) nc0 = read_ncount_body8 b (255 + 1) (repeat 0 256)).
  { intros b. unfold read_ncount_body8.
    replace (FseNCount.Zlength nc0) with (FseNCount.Zlength (repeat 0 256))
      by (unfold FseNCount.Zlength; rewrite HL, repeat_length; reflexivity).
    rewrite (zp_same (Z.to_nat (255 + 1)) nc0 (repeat 0 256)) by (first [rewrite HL| rewrite repeat_length]; reflexivity).
    reflexivity. }
  unfold read_ncount. cbv zeta. rewrite !HB. reflexivity.
Qed.

Lemma sh_ablk_out : forall X n a', ablk X (X + n) -> 0 <= a' < 2^47 -> ~ (X <= shad a' < X + n).
Proof.
  intros X n a' HB Ha. rewrite shad_div. unfold ablk, AIMG_HI, KLS in HB. unfold ASHOFF. Z.div_mod_to_equations. lia.
Qed.

Section Main.
Hypothesis RDK : fse_readk_stmtA AI rng_fs (S kk).
Hypothesis BDT : fse_build_stmtA AI.
Hypothesis SAFE : dec_stmtA 0x98664 0 false.
Hypothesis FAST : dec_stmtA 0x984e8 1 true.

Theorem fse_decomp_proofA : fse_decomp_stmtA AI rng_fs kk.
Proof.
  intros L RNG ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV DST dcap S W wks maxLog src jd jw lo rstk
    AH FK LBH JD JDL SRC SRCB JW JWL DC SRCL ML WK32 HDST HW W8 SRCH S16 DD1 DD2 DD3 STK BOT LO SPT SP16 RCL RLO RHI RRLO MI TP ZMK MKCI
    RSTK RI RISH RFS RRS.
  pose proof atop_range as ATR. unfold AFSE_DECOMP_STACK in LO.
  assert (WB : 0 < W /\ W + wks <= ATOP)
    by (destruct HW as (p & A0 & N0 & HIn & _ & HA & HB); pose proof (ablk_lin _ _ (LBH _ HIn)) as (? & ? & ? & ?);
        cbn [ab_addr ab_size] in *; unfold AIMG_HI in *; lia).
  eapply (fdw_open L RNG ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV DST dcap S (zlen src) maxLog W wks lo).
  all: try first [exact AH| exact FK| exact LBH| exact STK| exact BOT| exact SPT| exact SP16| exact MI| exact TP| exact RSTK| exact RI| exact RFS
                 | exact W8| (unfold FDW_OPEN_STACK; lia)].
  all: try (split; lia).
  - intros FF m3 junk j8 j64 j80 y5 y6 y7 y11 y12 y13 y14 y15 y17 y28 y29 y30 y31 HWK
      (F64 & FH & FC & RFF & RSFF & FFD & AH3 & MG3 & MI3 & FRB3 & HDR3 & SH3 & STL3 & STG3) FRA3.
    rewrite fdw_err1.
    destruct (fdhdr_split _ _ _ _ _ HDR3) as (F03 & _ & _ & F563).
    replace (shad FF) with (Z.shiftr FF 3 + ASHOFF) in SH3 by (unfold shad, ASHOFF; lia).
    eapply (fdw_close L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 st LB SPV DST dcap W wks maxLog lo FF
              (2^64 - ZSTD_error_GENERIC) src).
    all: first [exact AH3| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact MI3| exact SH3| exact F03
               | exact F563| exact FRB3| exact FRA3| reflexivity| exact STL3| exact STG3| exact BOT| exact SPT| exact SP16| exact RSTK| idtac].
    + eapply magree_mono; [exact MG3|]. intros a Ha. unfold AF_huf_fdw_top1.PAGf in Ha. exact (proj1 Ha).
    + unfold FDW_OPEN_STACK. lia.
    + destruct HDST as (p & A0 & N0 & HIn & _ & HA0 & HA1). exists p, A0, N0. split; [exact HIn| lia].
    + lia.
    + unfold fse_decompress_wksp. replace (wks <? 512) with true by (symmetry; apply Z.ltb_lt; exact HWK). cbn.
      split; [reflexivity| try unfold ZSTD_error_GENERIC; lia].
    + unfold ZSTD_error_GENERIC. lia.
  - intros FF m3 junk j0' j64 j80 y5 y6 y7 y17 y28 y29 y30 y31 HWK
      (F64 & FH & FC & RFF & RSFF & FFD & AH3 & MG3 & MI3 & FRB3 & HDR3 & SH3 & STL3 & STG3) FRA3.
    destruct (fdhdr_split _ _ _ _ _ HDR3) as (F03 & H24 & F483 & F563).
    pose proof (ablk_lin _ _ FH) as (FL1 & FL2 & FL3 & FL4).
    destruct (fdsh_unp _ _ SH3 F64 ltac:(lia) ltac:(lia)) as (U32 & U48).
    replace (shad FF) with (Z.shiftr FF 3 + ASHOFF) in SH3 by (unfold shad, ASHOFF; lia).
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
    pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & LY3 & _).
    pose proof HW as (pW & AW & NW & HInW & _ & HW1 & HW2).
    pose proof HDST as (pD & AD & ND & HInD & _ & HD1 & HD2).
    pose proof SRCH as (pS & AS & NS & HInS & HS1 & HS2).
    pose proof (FFD _ HInW) as FW. pose proof (FFD _ HInD) as FD. pose proof (FFD _ HInS) as FS. cbn [ab_addr ab_size] in FW, FD, FS.
    assert (BLK0 : forall b a, In b LB -> ab_addr b <= a < ab_addr b + ab_size b -> aclient_addr CI LB SPV a)
      by (intros b a Hb Ha; right; right; left; exists b; split; [exact Hb| exact Ha]).
    assert (TR3 : forall A l b, In b LB -> ab_addr b <= A -> A + zlen l <= ab_addr b + ab_size b -> u8arr bsegs m A l -> u8arr bsegs m3 A l).
    { intros A l b Hb H1 H2 (U1 & U2). split; [eapply bytes_at_magree; [exact MG3| exact U1|]| eapply wr_at_magree; [exact MG3| exact U2|]];
        intros a Ha; apply (BLK0 b a Hb); lia. }
    assert (JW3 : u8arr bsegs m3 W jw) by (apply (TR3 W jw _ HInW); [cbn [ab_addr ab_size]; lia| cbn [ab_addr ab_size]; lia| exact JW]).
    assert (JD3 : u8arr bsegs m3 DST jd) by (apply (TR3 DST jd _ HInD); [cbn [ab_addr ab_size]; lia| cbn [ab_addr ab_size]; lia| exact JD]).
    assert (SRC3 : bytes_at bsegs m3 S (map (Z_to_bv 8) src)).
    { eapply bytes_at_magree; [exact MG3| exact SRC|]. intros a Ha. rewrite length_map in Ha. apply (BLK0 _ a HInS). cbn [ab_addr ab_size]. lia. }
    clear TR3.
    pose proof (u16s_of_bytes 256 (firstn 512 jw) ltac:(rewrite length_firstn; lia)) as (rt0 & LRT0 & RTB0 & ERT0).
    pose proof JW3 as JWs. rewrite <- (firstn_skipn 512 jw) in JWs. apply RF_huf_bdt_model.u8arr_app in JWs as (JWa3 & JWb3).
    rewrite length_firstn, Nat.min_l in JWb3 by lia. change (Z.of_nat 512) with 512 in JWb3. rewrite ERT0 in JWa3.
    assert (ZRT0 : zlen rt0 = 256) by (rewrite LRT0; reflexivity).
    pose proof (rw_cells_split_CB bsegs m3 (FF + 24) [] 24 (firstn 24 junk) [] [8; 4; 12]%nat H24 eq_refl) as T3.
    cbn [app mk_CB_cells] in T3.
    pose proof (proj1 (ABytes.rw_cells_app _ _ _ [CB 8 _] _) T3) as (_ & T4).
    pose proof (proj1 (ABytes.rw_cells_app _ _ _ [CB 4 _] _) T4) as (T5 & _).
    apply (rw_cells_eqA _ _ (FF + 32)) in T5; [|cbn; lia].
    assert (TLC3 : exists tl0, rw_cells bsegs m3 (FF + 32) [C4 tl0]).
    { pose proof (cells_at_wf _ _ _ _ (proj1 T5)) as (WF & _). cbn [cell_wf] in WF.
      exists (le_bytes_to_word (firstn 4 (skipn 8 (firstn 24 junk)))). apply rw_cells_CB4_C4.
      rewrite ABytes.le4_of_bytes by exact WF. exact T5. }
    destruct TLC3 as (tl0 & TLC3). clear T3 T4 T5.
    assert (LBH' : forall b, In b (FB0 FF :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b))
      by (intros b [<-|Hb]; [exact FH| exact (LBH b Hb)]).
    assert (BW : bufH (FB0 FF :: LB) W 512) by (exists pW, AW, NW; split; [right; exact HInW| lia]).
    assert (RW : rng RNG W 512 /\ rng RNG (shad W) (nshad (512 + W mod 8))) by exact (AF_huf_fdw_top2.rng_bufH AI 0 0 _ _ _ _ _ W 512 AH3 BW ltac:(lia)).
    replace (512 + W mod 8) with 512 in RW by lia.
    assert (RS : rng RNG S (zlen src) /\ rng RNG (shad S) (nshad (zlen src + S mod 8))) by exact (AF_huf_fdw_top2.rng_bufH AI 0 0 _ _ _ _ _ S (zlen src) AH SRCH ltac:(lia)).
    eapply evtF_cut.
    { pose proof RDK as RD0. unfold fse_readk_stmtA in RD0.
      eapply RD0 with (m := m3) (LB := FB0 FF :: LB) (SPV := SPAf SPV) (NC := W) (MSVP := FF + 48) (TLP := FF + 32) (BUF := S)
        (rt0 := rt0) (buf := src) (msv0 := 255) (lo := lo) (tl0 := tl0); clear RD0.
      all: try replace (2 * zlen rt0) with 512 by lia.
      all: first [exact AH3| exact (fake0_lek_push0 _ FF 64 LB FK)| exact LBH'| exact JWa3| exact F483| exact TLC3| exact SRC3| exact SRCB
                 | exact W8| exact STL3| exact BOT| exact MI3| exact TP| exact RSTK| exact RI| exact RFS| exact (proj1 RW)| exact (proj2 RW)
                 | exact (proj1 RS)| exact (proj2 RS)| idtac].
      all: first [lia
                 | exact (bufA_of_bufH _ _ _ _ BW)
                 | right; exists pW, AW, NW; split; [right; exact HInW| lia]
                 | split; [do 3 eexists; split; [left; reflexivity| split; [lia| split; [lia| split; [exact FH| lia]]]]| first [exact U48| exact U32]]
                 | exists pS, AS, NS; split; [right; exact HInS| lia]
                 | eapply ablk_sub; [exact (LBH _ HInS)| cbn [ab_addr ab_size]; lia| cbn [ab_addr ab_size]; lia]
                 | unfold FSE_READ_STACK_A; lia
                 | eapply rng_sub; [exact RFF| lia| lia]
                 | eapply rng_sub; [exact RSFF| rewrite !shad_div; Z.div_mod_to_equations; lia| rewrite !shad_div; Z.div_mod_to_equations; lia]
                 ]. }
    cbv beta. intros ms' (t0' & t1' & t2' & a1 & a2 & a3 & a4 & a5 & a6 & a7' & t3' & t4' & t5' & t6' & r & m4 & -> & MI4 & STK4 & MG4 & AH4 & RES4).
    rd_retlit.
    rewrite (rnc_nc0 rt0 src LRT0) in RES4.
    assert (MG3' : magree bsegs (AF_huf_fdw_top1.PAGf AI LB SPV DST dcap W wks) m m3).
    { eapply magree_mono; [exact MG3|]. intros a Ha. unfold AF_huf_fdw_top1.PAGf in Ha. exact (proj1 Ha). }
    assert (P4 : forall a, AF_huf_fdw_top1.PAGf AI LB SPV DST dcap W wks a ->
       aclient_addr CI (FB0 FF :: LB) (SPAf SPV) a /\ ~ (W <= a < W + 2 * zlen rt0) /\ ~ (FF + 48 <= a < FF + 48 + 4) /\ ~ (FF + 32 <= a < FF + 32 + 4)).
    { intros a Ha. destruct (pag_rd LB FF SPV (SPAf SPV) DST dcap W wks 512 a HCI HCI0 FH ltac:(lia) ltac:(lia) ltac:(lia) LBH FFD Ha) as (A1 & A2 & A3 & A4).
      rewrite ZRT0. refine (conj A1 (conj _ (conj A3 A4))). lia. }
    assert (SHP : forall a, Z.shiftr FF 3 + ASHOFF <= a < Z.shiftr FF 3 + ASHOFF + 8 ->
       aclient_addr CI (FB0 FF :: LB) (SPAf SPV) a /\ ~ (W <= a < W + 2 * zlen rt0) /\ ~ (FF + 48 <= a < FF + 48 + 4) /\ ~ (FF + 32 <= a < FF + 32 + 4)).
    { intros a Ha. pose proof (AF_huf_fdw_top2.ffsh_pre 0 0 FF a F64 ltac:(lia) Ha) as Ha'.
      assert (EA : a = shad (8 * (a - ASHOFF))) by (rewrite (AF_huf_fdw_top2.shad_inv8 0 0); reflexivity).
      rewrite ZRT0. split; [| split; [| split]].
      - right; right; right. exists (8 * (a - ASHOFF)). split; [right; right; do 3 eexists; split; [left; reflexivity| exact Ha']| exact EA].
      - rewrite EA. exact (AF_huf_fdw_top2.sh_hblk_out 0 0 LB W wks W (2 * 256) (8 * (a - ASHOFF)) HW LBH ltac:(lia) ltac:(lia) ltac:(lia)).
      - rewrite EA. apply sh_ablk_out; [eapply ablk_sub; [exact FH| lia| lia]| lia].
      - rewrite EA. apply sh_ablk_out; [eapply ablk_sub; [exact FH| lia| lia]| lia]. }
    assert (PST : forall a, SPAf SPV <= a < SPV ->
       aclient_addr CI (FB0 FF :: LB) (SPAf SPV) a /\ ~ (W <= a < W + 2 * zlen rt0) /\ ~ (FF + 48 <= a < FF + 48 + 4) /\ ~ (FF + 32 <= a < FF + 32 + 4)).
    { intros a Ha. rewrite ZRT0. split; [left; lia| lia]. }
    assert (PFF : forall a, (FF <= a < FF + 8 \/ FF + 56 <= a < FF + 64) ->
       aclient_addr CI (FB0 FF :: LB) (SPAf SPV) a /\ ~ (W <= a < W + 2 * zlen rt0) /\ ~ (FF + 48 <= a < FF + 48 + 4) /\ ~ (FF + 32 <= a < FF + 32 + 4)).
    { intros a Ha. rewrite ZRT0. split; [right; right; left; exists (FB0 FF); split; [left; reflexivity| cbn [ab_addr ab_size]; lia]| lia]. }
    assert (PBL : forall b a, In b LB -> ab_addr b <= a < ab_addr b + ab_size b -> ~ (W <= a < W + 512) ->
       aclient_addr CI (FB0 FF :: LB) (SPAf SPV) a /\ ~ (W <= a < W + 2 * zlen rt0) /\ ~ (FF + 48 <= a < FF + 48 + 4) /\ ~ (FF + 32 <= a < FF + 32 + 4)).
    { intros b a Hb Ha Hn. pose proof (FFD b Hb) as Hd. rewrite ZRT0. split; [right; right; left; exists b; split; [right; exact Hb| exact Ha]| lia]. }
    assert (FI4 : AF_huf_fdw_top2.finv AI fflag L RNG ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m st LB SPV DST dcap W wks lo FF m4 j0' j64 j80).
    { refine (conj AH4 (conj _ (conj MI4 (conj _ (conj _ (conj _ (conj _ (conj _ (conj STK4 _))))))))).
      - eapply magree_trans; [exact MG3'|]. eapply magree_mono; [exact MG4| exact P4].
      - eapply rw_cells_magree; [exact MG4| exact SH3|]. intros a Ha. apply SHP.
        assert (FS8 : Z.of_nat (cells_size FDSH) = 8) by reflexivity. rewrite FS8 in Ha. unfold ASHOFF in *. lia.
      - eapply rw_cells_magree; [exact MG4| exact F03|]. intros a Ha. apply PFF. cbn in Ha. lia.
      - eapply rw_cells_magree; [exact MG4| exact F563|]. intros a Ha. apply PFF. cbn in Ha. lia.
      - eapply rw_cells_magree; [exact MG4| exact FRB3|]. intros a Ha. apply PST. cbn in Ha. lia.
      - eapply rw_cells_magree; [exact MG4| exact FRA3|]. intros a Ha. apply PST. cbn in Ha. lia.
      - eapply stk_magree; [exact MG4| exact STG3|]. intros a Ha. apply PST. lia. }
    clear MG3' P4 SHP PST PFF.
    destruct (read_ncount (repeat 0 256) 255 src) as [(((rt & msv) & tl) & ncl)| e | |] eqn:RD; cbn [fse_read_resA] in RES4; try contradiction.
    + destruct RES4 as (-> & RTW & MSC & TLC).
      assert (TR4 : forall A l b, In b LB -> ab_addr b <= A -> A + zlen l <= ab_addr b + ab_size b -> (A + zlen l <= W \/ W + 512 <= A) ->
                    u8arr bsegs m3 A l -> u8arr bsegs m4 A l).
      { intros A l b Hb H1 H2 H3 (U1 & U2). split; [eapply bytes_at_magree; [exact MG4| exact U1|]| eapply wr_at_magree; [exact MG4| exact U2|]];
          intros a Ha; apply (PBL b a Hb); lia. }
      assert (LSK : zlen (skipn 512 jw) = wks - 512) by (rewrite length_skipn; lia).
      assert (JW4 : u8arr bsegs m4 (W + 512) (skipn 512 jw))
        by (apply (TR4 (W + 512) _ _ HInW); [cbn [ab_addr ab_size]; lia| cbn [ab_addr ab_size]; lia| lia| exact JWb3]).
      assert (JD4 : u8arr bsegs m4 DST jd)
        by (apply (TR4 DST jd _ HInD); [cbn [ab_addr ab_size]; lia| cbn [ab_addr ab_size]; lia| lia| exact JD3]).
      assert (SRC4 : bytes_at bsegs m4 S (map (Z_to_bv 8) src)).
      { eapply bytes_at_magree; [exact MG4| exact SRC3|]. intros a Ha. rewrite length_map in Ha. apply (PBL _ a HInS); cbn [ab_addr ab_size]; lia. }
      clear TR4 PBL.
      eapply fdw_rd_ok with (mx := m4) (jd := jd) (jwr := skipn 512 jw).
      all: first [exact FI4| exact RD| exact RTW| exact MSC| exact TLC| exact JW4| exact LSK| exact JD4| exact JDL| exact SRC4| exact SRCB| exact HW
                 | exact W8| exact SRCH| exact S16| exact HWK| exact WK32| exact ML| exact SRCL| exact DD1| exact DD2| exact DD3
                 | exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact BOT| exact LO| exact SPT
                 | exact SP16| exact RSTK| exact HDST| exact DC| exact RI| exact RISH| exact BDT| exact RCL| exact RLO| exact RHI| exact RRLO
                 | exact RRS| exact ZMK| exact MKCI| exact SAFE| exact FAST].
    + destruct RES4 as (-> & HE & _).
      zstep. replace (Z_to_bv 64 (-120)) with (Z_to_bv 64 (2^64 - 120)) by (apply Z_to_bv_eqm; reflexivity).
      zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].
      assert (DR : dresA DST dcap (fse_decompress_wksp (repeat 0 256) dcap src maxLog wks) m4 (2^64 - e)).
      { unfold fse_decompress_wksp. replace (wks <? 512) with false by (symmetry; apply Z.ltb_ge; lia). unfold FSE_MAX_SYMBOL_VALUE. rewrite RD. cbn.
        split; [reflexivity| lia]. }
      eapply fdw_exit with (mx := m4) (rv := 2^64 - e).
      all: first [exact FI4| exact DR| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact BOT| exact LO| exact SPT
                 | exact SP16| exact RSTK| exact HDST| exact DC| exact RI| exact RISH| exact BDT| exact RCL| exact RLO| exact RHI| exact RRLO
                 | exact RRS| exact ZMK| exact MKCI| exact SAFE| exact FAST| lia].
Qed.
End Main.
End Asm.
End CANSEC1.
