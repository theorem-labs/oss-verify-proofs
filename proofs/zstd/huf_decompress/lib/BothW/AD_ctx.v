(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_iface F_printf_iface MonadF AF_atexit AExit F_module_dtor ADriver_iface AD_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AHarness_bm.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AD_ctx () := "C46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF6implAMC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor5gdescK47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?rw_cells_magreeK47Corelib4Init5Logic3and01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor6gdescsK47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic5proj1c5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx<gdesc_magreeC47Corelib4Init5Logic5proj2C47Corelib4Init9Datatypes8list_indC56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init5Logic4True01K46Stdlib9micromega:ZMicromega;ZArithProof01c5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx:astat_addrc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx5ASTATK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothW9AF_atexit:atx_stateAK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C46Stdlib9micromega;ZifyClasses6eq_iffI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5BothW9AF_atexit?atx_state_addrAc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx8astat_shC5ARocqVerifyHarness?AgentSubmission5BothW9AF_atexit@atx_stateA_agreeC47Corelib4Init5Logic6eq_indc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx=gdescs_magreeK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init5Logic6ex_indC47Corelib4Init5Logic7and_indC5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor8AGLOBALSC5ARocqVerifyHarness?AgentSubmission5BothW5AExit6RSTDINC5ARocqVerifyHarness?AgentSubmission5BothW5AExit;stdin_cellsC5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor?AGLOBALS_lengthc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx7astringC5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_lib2zbC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atI47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rhiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit>rclean_shcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit7shcleanC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6hull64C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7app_blkK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5inregC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atI5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00c5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx@implMA_of_implAMC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit6implMAc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx=astring_factsC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_lib9zb_lengthC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?bytes_at_magreeC5ARocqVerifyHarness?AgentSubmission5BothW6AProto9shad_monoC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kit=rclean_magreeC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr04I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op201c5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx3ALOC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>drv_img_rangesC56Stdlib6ZArith6BinInt1Z3divC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface;shad_unshadC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface>cli_img_rangesC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kit4dcliC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx5ABASEc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx7AMFRAMEC5ARocqVerifyHarness?AgentSubmission5BothW;Stdio_iface=stderr_wfile0C5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<atrun_cells0C5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:rodata_sh0C45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles;stdout_filec5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx:stack_dclic5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx9astat_appC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_donec5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx:ci_drv_sh'c5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx;ASTAT_agreeC47Corelib4Init5Logic6or_indc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx6ci_drvC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface<atrun0_addrAC5ARocqVerifyHarness?AgentSubmission5BothW9AF_atexit9atx_addrAC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_ifaceCatrun_cells0_magreec5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx9ci_drv_shC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kitArodata_sh0_magreec5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx=stack_sh_dcliC5ARocqVerifyHarness?AgentSubmission5BothW6AD_kitBstdout_file_magreeC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles:file_cellsC56Stdlib6ZArith6BinInt1Z4landI5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00I5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00C5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9ssp_guardC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit8RBstdoutC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface4RSTGC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx3geoC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface;ASTAGE2_RETC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface:AINIT_FLAGC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7AHBM_LOC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7AHBM_HIc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx>errno_addr_ATPc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx>astring_magreec5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx4WOKbC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx<WOKb_outsidec5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx3WOKC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4appWK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KLOWc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx9WOKb_appWC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?magree_of_munchC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface@rodata_sh0_frameC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit@rclean_transportc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx;WOK_outsidec5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx>ABASE_of_partsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem>bytes_at_boundC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_relroC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem:rw_bytes_bC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?rw_cells_image0C5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure?rw_cells_recastC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9ARELRO_LOC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9ARELRO_HIC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls7got_sspC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_rtcellsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8artcellsc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctxCexit_relro_of_aheapC5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor8mdtor_rtC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles;stderr_fileC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF4rng0C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface8aat_exitc5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctxAmdtor_rt_of_aheapC5ARocqVerifyHarness?AgentSubmission5BothW=F_module_dtor9mdtor_preC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps6aps_soC5ARocqVerifyHarness?AgentSubmission5BothW5AExit;MDTOR_DEPTHC5ARocqVerifyHarness?AgentSubmission5BothW5AExit7MDTOR_WC5ARocqVerifyHarness?AgentSubmission5BothW=ADriver_iface8AEXIT_PCC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releaseK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldK4ELinuxProcessSemantics5Riscv5Instr5instr03c5ARocqVerifyHarness?AgentSubmission5BothW6AD_ctx>aat_exit_introC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accK47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_lit".   
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].


Section CANSEC1. Context {rc : runConstT}.
Lemma implMA_of_implAM : forall {A} RNG (c : @Monad.M APS A) (s : APS) (Q : A -> APS -> machine_state -> Prop) ms,
  implAM RNG c s Q ms -> implMA RNG c s (fun a s' RNG' ms' => RNG' = RNG /\ Q a s' ms') ms.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"] "h01Ah11Hh21Qh33RNGh41ch52msh61sp;2p;7p-1p10000p4p710R0p8p200R1g000GR2p4p7210p8P1g0018R3p4p7210p8p10020p4p70P0p8p1002gp4p7210p1003Sp4p710p8P2j21TP3j70Tg0041g004jR3f1R2'1f3R0g005fR4p-0[\3[P3f5f4P0f2P2f0R2F0P2W1X54W2X63W4W3X01o"). Qed.



Section CTX.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  
  Variables (usp : Z) (TID : Z).
  
  Variables (S0 S1 S2 S3 S4 S5 S6 S7 : word) (J8 : list byte).

  Definition ALO : Z := usp - 8388608 + 4096.

  Definition AMFRAME (mm : amem) : Prop :=
    rw_cells bsegs mm (usp + -128) [CB 8 J8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 (Z_to_bv 64 ASTAGE2_RET)].

  
  Definition ASTAT (mm : amem) : Prop :=
       rw_cells bsegs mm 0x5ed1e8 [C4 (Z_to_bv 64 TID)]                                 
    /\ rw_cells bsegs mm 0x60d500 [C4 (Z_to_bv 64 0)]                                   
    /\ (exists cdt thr sec tm1, rw_cells bsegs mm 0x60d520 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])  
    /\ (exists reg : bool, atx_stateA reg mm)                                          
    /\ rw_cells bsegs mm 0xb6c90 [C1 (Z_to_bv 8 0)]                                   
    /\ (exists dso, rw_cells bsegs mm 0xb3e40 [C8 dso])                                
    /\ rw_cells bsegs mm 0x60d988 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs mm 0xb69c0 [C8 (Z_to_bv 64 RSTDIN)]  
    /\ rw_cells bsegs mm RSTDIN stdin_cells                                          
    /\ rw_cells bsegs mm 0xb68d0 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells bsegs mm 0xb67e0 [C8 (Z_to_bv 64 RSTDERR)]  
    
    /\ rw_cells bsegs mm 0xb7b10 [C4 (Z_to_bv 64 1)]
    /\ rw_cells bsegs mm 0xb6c40 [C8 (Z_to_bv 64 1)]
    /\ rw_cells bsegs mm 0xb7bb0 [C8 (Z_to_bv 64 0)]
    /\ gdescs mm 0xb69f0 AGLOBALS
    /\ (exists j, rw_cells bsegs mm 0x7fffc1c0 [CB 144 j]) /\ (exists j, rw_cells bsegs mm 0x8000ed3e [CB 72 j]).

  
  Definition astat_app (a : Z) : Prop :=
       (0x5ed1e8 <= a < 0x5ed1ec) \/ (0x60d500 <= a < 0x60d508) \/ (0x60d520 <= a < 0x60d530) \/ (0x60d2e0 <= a < 0x60d310)
    \/ (0x60d400 <= a < 0x60d410) \/ (0x14c1a0 <= a < 0x14c1a1) \/ (0x5ec954 <= a < 0x5ec955) \/ (0xb6c90 <= a < 0xb6c91) \/ (0xb3e40 <= a < 0xb3e48)
    \/ (0x60d980 <= a < 0x60d9a0) \/ (0xb69c0 <= a < 0xb69c8) \/ (0xb68d8 <= a < 0xb6968) \/ (0xb68d0 <= a < 0xb68d8) \/ (0xb67e0 <= a < 0xb67e8)
    \/ (0xb7b10 <= a < 0xb7b14) \/ (0xb69f0 <= a < 0xb6c30) \/ (0xb6c40 <= a < 0xb6c48) \/ (0xb7bb0 <= a < 0xb7bb8).
  Definition astat_sh (a : Z) : Prop :=
       (0x7fffc1c0 <= a < 0x7fffc250) \/ (0x8000ed3e <= a < 0x8000ed86).
  Definition astat_addr (a : Z) : Prop := astat_app a \/ astat_sh a.

  Lemma gdesc_magree : forall (P : Z -> Prop) m m' d b sz szr nm mn odr,
    magree bsegs P m m' -> (forall a, d <= a < d + 64 -> P a) -> gdesc m d b sz szr nm mn odr -> gdesc m' d b sz szr nm mn odr.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"] "h04__x1h14__x2h21ah31xh42Hah53Ha0h67__arithh74__ffh88__varmaph95__with:1mh;2AGh<2G1h=2G2h>1Hh?2HPh@1PhA1bhB1dhC2m'hD2mnhE1nhF2nmhG3odrhH2szhI3szrhJ1yp;1p;4p;2p;8p;6p;3p;9p;<p;Bp;7g006mj19Tg007Rj1UTg0080j1NTg008Sj1\Tg0095j4oTg00:0j23Tg00:Lj1BTg00:jj8MTg00;hj1OTg00<HR0j22Tg00<ej2;Tg00=Kj1?Tg00>@j1RTg00?9R1j1=Tg00?Yj10Tg00@8R2j28Tg00@TR3j2DTg00@oj1CTg00AMj4]Tg00B0j6ITg00BYj4HTg00C@j1[Tg00C`j2ZTg00D>j1YTg00D\j4XTg00E:j1WTg00EXj1VTg00FCj2GTg00Ffj4ATg00GQj2FTg00H4j3ETg00HWj1nTg00I9j2mTg00I[j2PTg00J5j2hTg00Jaj3gTg00K;j3fTg00KZj4dTg00LLl9QTg00MPj4cTg00Mkj1bTg00N`j3<Tg00O@j4eTg00P6l<aTg00P[lB`Tg00QAl<iTg00Qfj7jTg00RJj7kTg00Rnj8lTf3R4f2R5f1R6f0R7'2'8'Dp=51;67#bp=1g00SRR8f4R9A<8679<859<843<p=4g00TGR:P5P6P7Cep=:A<867p=>%07#0p=_%07#0#0#0p=^%07#0#0#0#0#0#0#0p=7g00U<R;/P7p=6g00UZR<P;P;P;P1P1f5R1P9P4P5P6P7M<ap=LP;P;P;P;P;P;P0P7P6P5P0P4P9P1f6R0f7R=f8R>f9R?MB`p=KP;P;P2P=P2P0P1P9P4P5P6P7M<ip=JP6g00V9R2g00VXR@P@g00W8RAP7g00WXFjp=@P5P2P@P@PAP6P7Fkp=TP4P2P@P@PAP5P6P7Glp=Sp-0\;g00X8R2#9RB#9#9RC#9RD#9#9RE#URF#N%UCRC#N#\[RGP:P?P>P=Co13>7P7P>%BEREC5f<RHP6O1[^2;f:RIP>P=P0P1P9P4P5GMP3f;R311F>RJ11F=RK11F0RL11F1RM11F9g00X]RN,1FROPO11F4%O8R8D4D47:?%BDRD,2?1;C0#?/>85:3P3PIP?P>P=P0P1P9GMP7f=R911FIR111F?R>PJPKPLPOPOPMP8D4D47:3f>RM12HD1;C?#?/>83:11FHRH11F3R?P1P>PJPOPOPKP8D4D4RK9:M9129DRL1;CI#?/>8RI5:MP:f@RPf?RQPMP9PKP0P613M7P7PM11F9PHP?P1P>POPOPJP8D4D4#R#=C5P=P613Q6RJg00Y;#0RO#0#_#^#7#7#7#7#7#7#7R>#=R1,2QR?,86RH'DPJP6PQPEC5R9PJPHPJP7X3;RHPEO1RF,2QRK,86%CJPH1867#CXJ;X3;RJP6P6%66RRP?PKPHPHPHP;P;g00YZ1267C]#6X:;XE;RKPQPQ%6QP1PFPHPH%=7#6X3<R<P>PE%6EELM:KGJEIP7CHP9g00Z>R9#OR>%[9R9P;1Z;5P6%Y;CXRF%W;R1%V;R?P;1G;2RSg00ZjRT1G;BRBCA,@?P;PBg00[QRU1F;E9E;SCA,@?5T?RV%n@R@PVCS1m?ARAP7P5g00\8RWg00\XRX'P1h75=gWXdAf;N6CdRNb7b8b9X0;X1;1376P6P7PEC51365P5P6PEC5RE[^0;^1;P7P4fAP6O3R4b6b5O2W4X2;M9QP:PPPQPMPLPIP0P712MDRM/37P7PM1;C3#?/>8#R#=C5P=P612QDRQ/36R=%=OR8,2QR3,86RC'DP=P6PQ%B2R2C5RMP=PCP=PHP2O1RC,2QR0,86%C=PHPJP6P6PRP3P0PHPHPHPKPQPQ%6QP8PCPHPHP<POP2%62ELM:KGJEIP7CHPMP>P9PFP1P?P;1F;D9E;SRSPTPBCA,@?P;PBPU1F;29E;SCA,@?5T?P@PVCSPAPNb7b8b9X0;X1;127DRD/36P6PDP2C5PE[^0;^1;P4b6b5O2W4X2;M9QCcW=W<P6P7O2n2001000000121000000W>W?W;XG;XD;XF;XI;XH;XA;XB;XCGW:W@o"). Qed.

  Lemma gdescs_magree : forall G (P : Z -> Prop) m m' d, magree bsegs P m m' ->
    (forall a, d <= a < d + 64 * Z.of_nat (length G) -> P a) -> gdescs m d G -> gdescs m' d G.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"] "p'0h01ah11mh21Ph31dh42m'h51zi001zh64__x1h74__x2h84__x3h91lh:1xh;1Gh<1pi011ph=2AGh>2HGh?2HPh@2HahA7__arithhB4__ffhC8__varmaphD5__withE4cstrhF1nhG2IHhH1bhI2mdhJ2nmhK3swrhL2szhM1yp;2p;1p;4p;3p;8p;<p;6p;=p;5p;Bp;7g00]8R0j2ATg00C@j1\Tg006mj17Tg007Rj1MTg0080j1YTg008Sj1wTg0095j4qTg00:0j22Tg00:Lj1JTg00]Xj30Tg00;hj1LTg00N`j3@Tg00^Wj46Tg00_7j2vTg00_Tj2rTg00:jj8TTg00<HR1j21Tg00`1j2KTg00?YR2j1?Tg00?9R3j1:Tg00`QR4j2;Tg00@8R5j28Tg00@Tj2<Tg00@oj1OTg00QAl<`Tg00B0j6_Tg00`nj1^Tg00aSj2]Tg00b<j2BTg00bej3~Tg00cNj3[Tg00d7j2}Tg00C`j2WTg00D\j4|Tg00E:j1{Tg00EXj1yTg00GQj2HTg00dcj1xTg00FCj2ITg00HWj1uTg00H4j3=Tg00eHj3UTg00I9j2pTg00I[j2QTg00J5j2oTg00Jaj3nTg00K;j3mTg00KZj4lTg00ekj4STg00fVj3jTg00g1l=iTg00goj3hTg00MPj4gTg00hJj5sTg00AMj4tTg00P6l<PTg00P[lBZTg00Ffj4VTg00Qfj7fTg00RJj7eTg00Rnj8zTf5R6f4R7f3R8f2R9f1R:f0R;'K#:';'1'8'<p=3P8g00U<R<P9P:C6=@7;p=4P9P<P:P;C6p=XP7P<P8P<P9P:C6P;C6p=>18:;,<9p=R1Q<;p=5P<P<g00YZP;Ctp=Ng00UZR=P=P<P<P2P3P3P8g00hlP9P:P;M<Pp=dP=P<P<P<P3P3P6P7P8P9P:P;M<Pp=cP<P<P<P<P<P<P4P;P:P9P4P8P7P6f6R4f7R3f8R2f9R>MBZp=bP<P<P<P<P<P<P1P;P:P9P1P8P7P6P4P3P2P>MBZp=aP<P:g00ZjP;CVp=DP:g00V9R1g00VXR?P?g00W8R@P;g00WXFfp=9P<P:g00[QP;CVp=GP9P1P?P?P@P:P;Fep=FP8P1P?P?P@P9P:P;Gzp=C1;:;,19,88,<7p=E1K:;#:p=k1A<<R1/A<RA/A<RB/A<RC#\RDPCp-0\<REg00X8RF#7RG#7#7RH#7#7#7RI#M#Y%MH#Y#w[RHg00TGP8P9P:CqRJ129;RKP;P9%JIRIPCP4E3P4P:O1RL[^0<A0794A0783[[[^3<^4H]1]2RMX;DPKP;P9PIPC%LCRNE3PL[^0<A079Ng00iPA078NeW>W?X=JX3<X4HX1HX2EP0PBP<PKP;P9PIPCA@C23RNE3PL[^0<A079NA@C>29078[[\J^3<^4H^1H^2E\M^9DP;P0PAP<PKP;P9PIPCPCPBP>P2P3D4RNE3PL[^0<A079NPCPBf:RNP>P2D49078[[\J^3<^4H^1H^2E\M^9D^5<P;P0P1P<PKP;P9PIPCPCPBAXAN>P2P3D4ROE3PL[^0<A079OPCPBf;RO=XANP>P2D49078[[\J^3<^4H^1H^2E\M^9D^5<^5<P;P0P<P<PKP;P9PIPCPCPBPAP1POPNP>D>P2P3D4R0E3PL[^0<A0790PCPBPAP1f<R0POPND>P>P2D49078[[\J^3<^4H^1H^2E\M^9D^5<^5<^5<P;PKP;P9PIPCPCPBPAP1P<P<P0POC6PNP>D>P2P3D4RKE3PL[^0<A079KP7P8f=RKP0POPNP>%JG/vI%JFRL'rRPGT118IRQ=072P4P6P7P8PKP0POPNP>PPP9127;117IRR7R;P8P:126:RS1KCNRT#?RU#:RV,;IRW,16RX,8:RY'<RZ%:TR[/1LR\,;IR],16R^,8:R_,<SR`PSPYPSP_%OSP<P<P5P;X:<RSP518:;#OXM<X:<P:P:%5:PXP^PSPSPS11:;#N#5X1<XF<P6P6%56PWP]PSPSPS1;:;#N#5X1<XF<PIPI%5IPVP\PSPS%:;#5X:=PUP\11;LX:<PTP[%5[CdEcM:bM:aM<`E_R\%^TRTg00X]RU/2[R[g00Z>R=1]<Ig00Y;RS#?RV#?#?,B<5~<1B<V1B<S5[<5[<g00il'}%L=RS3@%\=R=P<1W<9P:1W<8C|RV%{<R]%y<RW1H<U%xF,I<R^'D,9W%u?R?PW1I<FRF1I<GRG'D,9WRX1H<IR59=<FR_,GG,9W5FWP?1H<L9=<^9U<59=<F,GG,9W9FWXRXCCCC1pW@R@P;P9g00\8RFg00\XRY'Q1o;9=nFYdAm<U:ClRYbBbCbDX6<X7<X8<12U912:9RU11:I7R91298P8P9PI117LDE[[^6<^7<^8<P;1kC0RFP8P3P:P9O5bAbECSO2W@X0<P6P8PKP0POPNP>PPGTRPA06Q2Ra;j;M=iP3P4P6P7PQP912R;P;PRPIPCP>E3P8P:PZP`P\PTP[PSP=PVP]PW1D_G,9WAU<5^9=<_,GG,9W5FWP?PXCCP@PYbBbCbDX6<X7<X8<11;IRY/2:P:PYPIP9DEPUP9P:PI118LDE[^6<^7<^8<P;PFP8P3P9O4bAbECSO2W@X0<AhPa;O7CgPCPBPAP1P<P<PKP0C6POPND>P>P2D49078eW>W?X=JX3<X4HX1HX2EXGMX;DXI<XJ<XK<XL<XH<P:P;O2n2001101010121100100X<1P:P;O2n2001101010121101100X<AP:P;O2n2001101010121101100X<BP:P;O2n2001101010121101100X0CP;DsW;o"). Qed.

  Lemma ASTAT_agree : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, astat_addr a -> P a) -> ASTAT m -> ASTAT m'.
Proof.
intros P m m' AG HP ST. unfold ASTAT in *.
Ltac tr1 AG HP := eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; apply HP; unfold astat_addr, astat_app, astat_sh; cbn in Ha; unfold RSTDIN in Ha; lia].
decompose [and ex] ST.
repeat match goal with
| |- _ /\ _ => split
| |- exists _, _ => eexists
end.
all: first [ tr1 AG HP
| eapply atx_stateA_agree; [exact AG | intros a Ha; apply HP; unfold atx_state_addrA, atx_addrA in Ha; unfold astat_addr, astat_app; lia | eassumption]
| eapply gdescs_magree; [exact AG | intros a Ha; apply HP; rewrite AGLOBALS_length in Ha; unfold astat_addr, astat_app; lia | eassumption] ].
Qed.

  
  Definition ASTATX (mm : amem) : Prop := exists reg : bool, atx_stateA reg mm.

  
  Definition astring (mm : amem) (P : Z) (s : list Z) (slack : list byte) (r : region) : Prop :=
    bytes_at bsegs mm P (zb s ++ Z_to_bv 8 0 :: slack)
    /\ Forall (fun c => 0 < c < 256) s
    /\ ((- (P + zlength s + 1)) mod 8 <= zlength slack)
    /\ (zlength s <= 131071)
    /\ usp + 24 <= P
    /\ rclean mm r /\ inreg r P (zlength s + 1 + zlength slack) /\ usp + -128 <= r_rlo r.

  Lemma astring_facts : forall m P s slack r, astring m P s slack r ->
    usp + 24 <= P /\ P + zlength s + 1 + zlength slack <= r_hi r /\ r_lo r <= P /\ usp + -128 <= r_rlo r /\ r_rlo r <= r_lo r
    /\ r_hi r <= r_rhi r /\ r_rhi r <= 2^47 /\ 0 <= zlength slack /\ 0 <= zlength s <= 131071.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"] "h04__x1h11Hh27__arithh34__x2h44cstrh55cstr0h64__ffh74__p1h88__varmaph95__with:4__p2h;4__p3h<4__p4h=4__p5h>4__x3h?4__x4h@2BYhA2HFhB3HULhC2IRhD3LENhE2LOhF1PhG2RChH3RLOhI2SLhJ2_HhK3_H0hL3_H1hM1chN1mhO1rhP1shQ5slackp&0p;1p;5p;2p;3p;4p;7p;8p;6g006mj14Tg007Rj1aTg0080j1hTg008Sk10:Tg00C@j1dTg01;Ck503Tg01<<j1kTg00<ej2vTg00N`j3lTg01=7j3iTg01=Tj4gTg00@8j2fTg00:Lj1CTg00@TR0j21Tg01>Ij3[Tg01>jj1MTg01?Gj2GTg01?gj23Tg00:0j20Tg00dcj1VTg00<Hj2;Tg01@_j1uTg01A=j15Tg01B6j17Tg01Boj16Tg01Cij18Tg00_7j2pTg01Dcj2]Tg01E^k309Tg01Fak508Tg01G]j3nTg01HXj4\Tg01ISj1=Tg00_Tj2LTg01JKj2QTg00`1j2STg00?9j1TTg00`nj1mTg00;hk106Tg00C`j2ZTg00D>k105Tg00D\j4cTg00E:k102Tg00EXk101Tg00FCj2YTg00HWj1~Tg00I9j2}Tg00I[j2|Tg00J5j2{Tg00Jaj3`Tg00K;j3yTg00KZj4xTg01KCj3zTg00GQj2jTg00MPj4^Tg01Kfj3bTg01L`j4tTg00H4k300Tg00Ffj4sTg00Qfj7rTg00Rnk804Tg015Fj6qTg00RJk707Tf0R1#4#4p=eg00U<R2/31p=2f2R3f1R4';/;1p=9%V1#Vp=B%61,04p=<f5R5f4R6']f3R7?b34/11'1p=P10671034/11'1p=:1141,13p=>g00X]R8/031041'1p=?f7R9f6R:'0105610731084/11'1'1'1p=@109:1;56/;7/;3/04/11'1p=A1;73/;49b56/11p=K10671]34/11'1p=U1;419b73p=og00TGR;P3P4P1Ctp=O1;34/01p=I1081p=J1j21p=NB00241p=FP3g00V9R<g00VXR=P=g00W8R>P2P4g00ZjP1Csg00WXFrp=EP7P<P=P=P>P3P4P1L04p=HP4P<P=P=P>P1Eqp=RP3P<P=P=P>P4P1K07p=D1041,13p=_%41#4#4#4p=w%41#4#4#4#4#4#4#4p=WP:P5P6P7P3P4P1C^C^p=Xg00X8R<#4R?#4R@#4RA#4#eRB#a#h%aARC#hRD$0:[%d2%dDg01MRP6P7P3P4P1I03P0P;P5P6%k71vC8RC=lD35iDCg1f81%4BRE#4RF#C,f1'1XM2RG=[27%27RH%C<RI596#M%CARA'G13D3RJ'0PH%V<RK#V#B#B#B#B#B#B#B#CRLp,3uspRM%4K#e#CRN';ROP6P5P4P4P6A9HIJ%uERE,;MRJ/<4EPD:3>POP5P5%26RHPI13D7RP%53RQ%73RRP5PJ%63RSPSPRPQ%83RQPQ%C?RQ%B?#BRR#C'pRSPPA?HHLG@D:GAP1P;P9P:%k5AlDC65iDCgA[2G:%2:RC=99I#M/GA13D5R;'0PCPLPOP9f8RHP6P6P9A9CI;1<J6EPD:3>P0A[2G9%29R;=9HI#M/GA13D:RCP;PLPOPHf9RPP5P5PHP;PIPC1<J5EKDUD:POPPPP%2HRCPI13D9R;%5:RT%7:RUPPPJ%6:RVPVPUPT%8:RTPTPSP;A?CCLG@D:GAP1A[2GPf;RGf:RC#2R;;9I#M/GA13DPRTP;PLPOPGf<RUPHPHPGP;PIPT1<JHEKDUD:P0%2GRT=9UI#M/GA13DCR;'0PTPLPOPUf=RVPPPPPUA9TI;1<JPEPD:POPVPV%2URPPI13DGRG%5CR;%7CRTPVPJ%6CRWPWPTP;%8CRCPCPSPGA?PPLG@D:GAP1f>RP%2V;9I#M/GA13DU'0%2PRAPLPOf?RGf@RCPUPUPG13DV99AI1<JUEPD:P0%2GRU/0LPOPCfARAPVPVPCPUPI13DP1<JVEKDUPOPAPA%2CRVPI13DGRG%5PRU%7PR;PAPJ%6PRTPTP;PU%8PRPPPPSPGA?VVLG@D:GAP1%2A/0LPOfCRVfDRGPCPCPVfBRP#2PI13DA1<JCEKDUP010OGfERUPAPAPG%2V13DP79I1<JAEPPOPUPU%2GR;PI13DVRV%5PRT%7PRWPUPJ%6PRXPXPWPT%8PRPPPPSPVA?;;LG@D:GAP1fFR;,0OfHRVPGPGfGRP%2;13DU79I1<JGEPP0fIRG/]UPUPV%2PPI13D;1<JUEKPOPGPG%2VRUPI13DPRT%5;RW%7;RXPGPJ%6;RYPYPXPW%8;R;P;PSPTA?UULG@D:GAP1fKRU/]PPVPUfJRP#2PI13DG1<JVEKP0PGfLRV%2U/;I13DPCo1<JGPOfMRTPT%2VR;PI13DURW%5PRX%7PRYPTPJ%6PRZPZPYPX%8PRPPPPSPWA?;;LG@D:GAP1PUfNRU%2T/;I13DVCo1<JVfQRV@09T5PV%7T%5T%6T%8TI08P0fRR;%7URW%5URP3nPWPP%6URX%8URUC\%=XRX%=U/LX5O;1QWP3>POP;P;%2VRPPIfPRW,3DRXfORU#5RY%7URZP;PJ%6UR[P[PZPY%8URUPUPSPXA?PPLG@D:GAP1fTRP%7W%5W3n%7VRW%5VRX%6VRU%8VRVC\fURY%=URU%=V/LU3O1QWX3>P0%7;RX%5;RW%6;RU%8;R;C\fVRV%=URU%=;/LU3O1QXW'1POPVPV%2YRWPI13DPRXfSRU#5R;%7URZPVPJ%6UR[P[PZP;%8URUPUPSPXA?WWLG@D:GAP1%7P%5P%6P%8PC\fYRP%6Y#=RW%8Y#=/LW3O%7Y%5Y'Q'1P0fZR0%6V#=RY%8V#=/LY3O%7V%5V'QPOP0P0%2PRVPIfXRY,3DRWfWRX#5RU%7XR;P0PJ%6XRZPZP;PU%8XRXPXPSPWA?VVLG@D:GAP1f\RV%6Y#=RW%8Y#=/LW3O%7P%5P'Qf]RP,0ORO1S2VRW#TRY=9PIf[RX,SD#TRU%50R;3IRZ%70R[/0PR\%60R],0JRJ10][R]%80R0,0;R[100SR0%JURU%JYR^10YLRY'1R_'1R`'1Ra'1Rb'1Rc'1Rd'1Re'1%mWRWP^1SDVRf#mRg%Tf#JRfg00Z>Rh$06Ri%dhRhP21Z23P4&052RjCcRk&022Rl&012Rm1Y2<R<%NN'F1Y2?R?5EmRn%~=R=PnCH1}m>R>P1P3g00\8Rng00\XRo'|1{13=`nodAy284CxRob6b8b9X02X32AI1N4AI4N3[^02^32P1f`RNPMPGO3b2b5b4PZPePWP^PgPfp-0RePiPhP2P21Z26P3PjCcP41Z27CcPlPm1Rm:R:%NIRj,F?1Y2KRK'F,F<1Y2@R@5Em5DmP=1F<?/Fj/FK=Em@CHP>Pob6b8b9X02X32X>2X?2W7A94I3,;1=_67A943I?I76[^02^32^>2^?2^7eP1%7PR@/0N%5PRKf^,SD#TRjf_,S2#TRZPNPAO6b2b5b4P\PdPWP^PgPfPiPhPkPlPmAEm<?Rd1Rm6RG5DmP=PdCHP>Pob6b8b9X02X32X7eRn1014Rp/131043Rq[^02^32^7eRrP1A9ZIj=INKPNP@PAO4b2b5b4PJPcPWP^PgPfPiPhPkPlPm%NE,F<=Em?R?P=P?CHP>Pob6b8b9X02X32AI1E4AI4E3[^02^32P1%6PREPMPCO3b2b5b4P]PbPWP^PgPfPnPrP1%8PRr,0KRn%CBRB,GE=`28Rb1GrB=`28RB%JERC%4F#e#w#W#W#W#W#CRF7_r3>RM'1P@PEPHO4b2b5b4P[PaPWP^PgPfPiPhPkPlPm1Rm5Rk9Dmd9DmGP=PdCHP>Pob6b8b9X02X32X7eX:eA>3p7Pq[^02^32^7e^:eP1PM10E@REPrPKPHO5b2b5b4P0P`PWP^PgPfPiPh1Z24R`PlPm1Rm71Rm9%NF9Em<5Dm9Dm:9Dmk9DmG5DmP=%NQ%aR5z29Em<CHP>Pob6b8b9X02X7eX:eX;eX<eX=eA_51F9>769>43104S[^02^7e^:e^;e^<e^=eP1PCPBPbPnPEPrPHO7b2b5b4PUP_PWP^PgPfPiPhP`PlPm1j28=Em<R8P=P8CHP>Pob6b8b9X02R8%J1%J4[^02R_P1PjP4O2b2b5b4P^PYPWP^PgPfP8P_P1PZP3O2b2b5b4PWP^PgPfPiPhP`PlPm%NL9Em<R<P=P<CHP>Pob6b8b9X02101L104L[^02P1PZPTO2b2b5b4C^FXFXFXFX%2VRV=9PI13DXRX;I;%JXA?VVL5>09>][9>\J5>OeWLWKP4P1O2n2001000000121000000W1WBP4P1O2n2001000000121000000W1WJP4P1O2n2001000000121000000b1WHWCP4P1O2n2001000000121000000W1WGP4P1O2n2001000000121000000W1WEP4P1O2n2001000000121000000W1WDP4P1O2n2001000000121000000W1WIP4P1O2n2001000000121000000W1WAP4P1O2n2001000000121000000W1W@P4P1O2n2001000000121000000W1WOWQWPXF2WNo"). Qed.

  Lemma astring_magree : forall (P0 : Z -> Prop) m m' P s slack r,
    magree bsegs P0 m m' ->
    (forall a, usp + -128 <= a < 2^47 -> P0 a) -> (forall a, shad (usp + -128) <= a < shad (2^47) -> P0 a) ->
    astring m P s slack r -> astring m' P s slack r.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"] "h01Hh14__x1h24__x2h32Hah47__arithh54__ffh68__varmaph75__with84__x3h94__x4h:4__x5h;1ah<1xh=1nh>4__x6h?4__x7h@1mhA2AGhB2AShC2BYhD2F1hE2F2hF2F3hG2F4hH2F5hI2F6hJ2F7hK2F8hL2F9hM2H0hN2H1hO2H2hP2HFhQ3Ha0hR2IRhS3LENhT2LOhU1PhV2P0hW2RChX3RLOhY2SLhZ1ch[4cstrh\2m'h]1rh^1sh_5slackh`1yp%0p&0p;1p;4p;2p;5p;6p;3p;<p;9p;7p;Bp;8p101NOp6051001p101OQp4p710p8g006mj1>Tg007Rj1jTg0080j1pTg008Sk102Tg00C@j1iTg0095k40NTg01@_k10JTg00<HR0j22Tg00:Lj1KTg00dcj1JTg00_7j2}Tg01ISj1ITg01;Cj58Tg01PLk60OTg01?gj23Tg01A=j1<Tg01B6j1?Tg01Boj19Tg01Cij16Tg00:0j20Tg01<<j1VTg00<ej2|Tg00N`j3@Tg01=7j3\Tg01=Tj4fTg00@8R1j2RTg01>Ij3^Tg01>jj1QTg01?Gj2MTg01Dcj2]Tg00@TR2j25Tg00`1j2=Tg00?9R3j1ATg01QKj2dTg01Qbk30MTg013kj6wTg01RAk10LTg00?YR4j1PTg00@oj1vTg00AMk40ITg00QAm<0ATg00B0k60@Tg00BYk40?Tg00`nk10=Tg00b<j2oTg00d7j2bTg00;hk10;Tg00D>k10:Tg00E:k108Tg00EXk107Tg00GQj2aTg00HWk106Tg01KCk305Tg00FCj2lTg00I9k204Tg00I[j2nTg00J5k203Tg00Jak309Tg00K;k301Tg00KZk400Tg01SCm90>Tg01TGj3qTg01UBj7~Tg00MPj4LTg01Kfj3gTg00P6l<kTg00P[lBsTg00cNk30CTg00C`k20DTg00D\k40ETg00Ffj4tTg00Qfj7uTg00H4j3{Tg00RJj7zTg00Rnk80KTf0R5#J#Jp=Gf3R6f2R7'0f1R8/R5'5p=Eg00U<R9/35p=11278/25p=7g00X]R:/071085'5p=;106710:8/55'5p=Nf4R;/061078/55'5p=410:710:8/55'5p=m1278/05p=S1378,0:/55p=U%95,08p=:%<8/05p=x1385,0:p=r1R85,57p=[f5R</];Ag678/55'5p=Z1585,57p=y1267/289g<;/55p=X10;61]78/55'5p=e12859g67p=h1n95p=Wg00UZR=P=P9P9P4P3P3P6g00hlP7P8P5M<kp>0HP=P=P=P9P9P9g01VAP3P3P3P0g01VaP<P;P6P7P8P5MBsp>0GP=P9P9P9P3P3P<P;P6P7P8P5M<kp>0FP9P9P9P9P9P9P0P5P8P7P0P6P;P<f6R0f7R3f8R4f9R>MBsp>0B10:5p>0<1o95p=TB0C985p=O20D95p=YP9P7P8P5H0Ep=C1l95p=FP7g00V9R?g00VXR@P@g00W8RAP9P8g00ZjP5Ctg00WXRBFup=BA{985p=HP9P8g00[QP5Ctp=cP8P?P@P@PAP5PBFup=_P7P?P@P@PAP8P5Fzp=`P6P?P@P@PAP7P8P5L0Kp=Dp-0\9g00X8R?#>RB#>RC#>RD#>#>#>RE#j#p%jDRF#pRG$02[RH%i9%iGg01MRg00TGRIP0P<P;H0Np,3uspRJ%>ERE$0JRK'2RLP5P5%KBRM%JBRN#J#GRO#K'}RPCEP>P8O1[^;9%ILRQP5P5%IPRRCEf:RSP8O1[^;9P4P0P<P;P6D8P>P3P0P<P;P5J0O%J?RT#>RU#>#>#KRV,2JRWP3%10RX,23%K?RY13G<RZ37%<;R[%?;R\P3PL%9;R]P]P\P[%6;R[P[PPPZ%JTRZ#G#G#G#G#G#G#G#KR[9;XXCND4D4D4P210W4%13RX,2413G0R\77Y%<<R]%?<R^P4PL%9<R_P_P^P]%6<R]P]PP10X[9m\XD4D4D4PSP>P4P3P0D8P510WSf;R\%1SRX'213G>R]77Y%<4R^%?4R_P\PL%94R`P`P_P^%64R^P^PP10X[9m]XD4D4D4P2f<R]%1\RX;7Y13GSR^%<>R_3S%?>R`P]PL%9>RaPaP`P_%6>R>P>PPP^A;XX[CND4D4f>RXf=R^P]P\PSD8P5%1^=7XY13G]%<\3S%?]R\f?RSPL%9]R>P>P\%<]%6]R]P]PP13G^%1XR]?;][CND4D4P2%?^R]f@R\'0PL%9^R>P>P]%<^%6^R]P]PP%1SR]?;][9UGXD4D4fBR]fAR>P\PSPXD8P5%?S/0]PL%9\RSPS%?\%<\%6\R\P\PP%1]R\?;\[9UG>D4D4P2%9>R\,0LP\%?>%<>%6>R\P\PP13G]fCR\#1RS?;S[CND4fFRSfERXfDR_P\P]D8P51:L\%9_%?_%<_%6_R_P_PP13GX%1SR_?;_[CND4P2%9X%?X'0%<X%6XR_P_PPfGR_#1R\?;\[9UGSD4fJR\fIR]fHR`P_PSD8P5%9_%?_'0%<`%6`R`P`PP%1\R`?;`[9UG]D4P2%6]R`,x]P`PP13G\fKR`#1R_?;_[CNfNR_fMRSfLRaP`P\D8P5%6`,x`%6aPP13GS%1_Ra?;a[CNP2%6S/0PfORS#1Ra?;a[9UG_fRRafQR`fPPSP_D8P5%6S/0P%1aRS?;S[9UG`P21rGafSRS#1R_?;_[fVR_fUR\fTRbPSPaD8P51rGb%1_Rb?;b[P2PIfZRbfXRafWRS#V1|F:RF=@G_5\GCf1R:5%>E#K7[5XZ9RE=^9S%1SRc=7aY#Q%KDRd'M13G_Re'0PcP[PWPaPbP\P\PaA7cYe1:L\EZD43yPbfYRePaPSP_D8P`PIf\R`Pb%VeA@GFa5\GCfA^9Ebf[R_%1bRS;7Y#Q/Md13GeRc'0PSP[PWP_f]RfPaPaP_A7SYc1:LaEZD43yP2A^9E_%1_Rc=7`Y#Q/Md13GbRSPcP[PWP`f^RgPePeP`PcPYPS1:LeEXDeD4PgPfP`P_PbD8P5A^9Eff_Rb%1gR_;7Y#Q/Md13GfReP_P[PWPbfaRSP`P`PbP_PYPe1:L`EXDeD4P2f`Re%1bR_;7Y#Q/Md13GgRc'0P_P[PWPefbRhPfPfPeA7_Yc1:LfEZD4PhPSPePbPgD8P5%1S=7hY#Q/Md13Ge'0%1hRgP[PWfcRbfeRcPePePb13GS97gY1:LeEZD4P2%1bRe/0[PWfdRgffR_PSPSPgPePY13Gh1:LSEXDeP_PcPgPbPhD8P5%1c/0[PWfgRhfiRbPgPgPh%1_PY13Gc1:LgEXDeP2fhRg,0WfjRSPcPcPg%1h13G_77Y1:LcEZPSPbPgPhP_D8P510WSfmR_PgPgfkRh%1S13Gb77Y1:LgEZP2fnRg/]bPbflRc%1hPY13GS1:LbEXPgP_PcPhPSD8P5fpRS/]hPcfoRh%1gPY13G_1:LcEXP2P_PS%1h/2Y13GgCh1:L_frR_fqR2PSPhPgD8P5PhP_%12/2Y13GSCh1:LSPIfuRhftRgfsRe#VA@GF_5\GRiCfA^9EeS00%1eRE=7gY#Q/Md13G_Rd'0Rj10E[R[10WgRW1]h2RkP2Pg12EYPdChS011:L2S02'5Rd'5RE'5Rl'5Rm'5Rn'5PIfwRIfvRoPhPgPiPSP]PhP5P5%VgA@GFe5\G,=G#A,2hCEP=%VhR]A@GFgRi5\G,=G10I7Rp%A5Rq,2I7[7X==P51=G]1=Gi'dRrB0MG]iEwPoP8P8%Ar,2oCEP=%Vo,=GfxRr/06RiA@GFo,=G,d5#A,2r7[6X==P51=9oR]&0LoEwA@GFh,=G,d]#A,2I9[p7PeP61=9IRp1=GoR]#PRF'dRs#ARt,2rRu,R6Rv,5i%ApRw%A]Rx/2Y'2,2r9[i6RyPiPvPiP5X<9Rv125YX<9RzPxO1R{,2wR|O1R},2rR~,R6%viP9P9P1PvP11R85#vX`9X<9P6P6%W6PuP~PvPvPvP9P9g00YZ1285H0I#WX@9X=9PrPr%WrPtP}PvPv%WqX<=PsP|PpPw%WwPFP{PzP]Px%WxH0HJ0GJ0FN:0BN<0AJ0@P5H0?Py1=9rRy$0=%Ay$0<g00Z>Ryg00Y;Rx#PR]#PRz#PR{#PRF#PRw#T%TFRF%T{%Tz1o9xRx'O'ORz'O'Og00ilR{'b%Pw#T%T]/OxRx'O/b{&0;yR]5@y3@%iyRw%Y0&0:9Rp7C6%Y3?C<p7C7%Y;R|?C3p7C8&089Rs&079R=%FURq%FBRB5B=%FNRv%FCRC1a9YR}'H'H,Hq,cB,_=5`=&06@R@P=%>N#FRN1a9M%jO6059RO5B=P@P=%FDRD=B=NP@P=1Hqv/H}/HC=B=DP@P=1l9?R?1a9V'H=B=qP@1a9K,H?=B=BRq1cBO,_=5`=CDCDCDCDCD204=ARAP5P7g00\8RDg00\XRC'n20357>09DCdB019:8H00R:b5b6b7X19X29X89X99X:9X>9X?9P;P8P8127Y,26,2;CE103P1034A730Y?S<4AS;V412<KP0P0PPCE[[[[[^19^29^89^99^:9^>9^?9P5%6r%<rf{fz,=9#Afy,=G#AP0PJP7PaP`PcPSO<b4b[bQPLP6P6PPCEeO2b3b3W3X;9N90>Q00PnPXPjPmP>P[PlP^PWPEPbPkPdPIPoPhPSP2%9_#IP5P5%6_#ICEPSP8%9eRSP]Pw%Y7?C8pPsP=PqP@PqCDPAP:b5b6b7X19X29AS5K8AS8K7[^19^29P5%9gPJP6O3b45qL%IS,0Q%6gRSP]Pw%Y8PsP=AB=?OROP@POCDPAP:b5b6b7X19105P108P[^19P5%6hP\O2b47qP%IS/0R1OFx/b{1bz{=@y]5@yPw%Y<9Cp<9Cp7ACp<|?C6p7C8PsP=%>Z#FRZ%FTRT5B=P@P=%JU#FRU9B=?P@P=AB=UB1cBZ,_=5`=P@AB=?B1cBT,_=5`=CDCDCDPAP:b5b6b7X19X29X89X99X:910;7108;P<P6P6P0CEP6P;P;P<CE[[[^19^29^89^99^:9P5%6o#I%9o#IPRP;PQP8P7P6O8b4bMb0O2W3X;9P<F~Q01Q02P8PfCLCLCLCLCLCLCLPhPgPeP_P2D8eWXWRP8P5O2n2001000000121000000W0WWP8P5O2n2001000000121000000W0WTP8P5O2n2001000000121000000W0WSP8P5O2n2001000000121000000W0WYP8P5O2n2001000000121000000W0WPP8P5O2n2001000000121000000W0WCP8P5O2n2001000000121000000WLWKP8P5O2n2001000000121000000W0WJP8P5O2n2001000000121000000W0WIP8P5O2n2001000000121000000W0WHP8P5O2n2001000000121000000W0WGP8P5O2n2001000000121000000W0WFP8P5O2n2001000000121000000W0WEP8P5O2n2001000000121000000W0WDP8P5O2n2001000000121000000b0WBWOWNWAW]W_W^XU9X\HW@WVo"). Qed.

  
  Variable RSTK : region.
  Hypothesis RSTK_lo : r_lo RSTK <= ALO.
  Hypothesis RSTK_hi : usp + -128 <= r_hi RSTK.
  Hypothesis RSTK_rlo : ATOP <= r_rlo RSTK.
  
  Hypothesis USP16 : usp mod 16 = 0.
  Hypothesis USPLO : ATOP + 8388608 <= usp.
  Hypothesis USPHI : usp + 24 <= 2^47.
  
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv CI.
  Variable canary : word.

  
  
  Definition ABASE (so : stdout_st) (mm : amem) : Prop :=
    stk bsegs mm ALO (usp + -128) /\ mem_inv bsegs mm /\ AMFRAME mm /\ ASTAT mm
    /\ stderr_wfile0 mm /\ rw_cells bsegs mm ssp_guard [C8 canary]
    /\ atrun_cells0 mm /\ harness_invA mm /\ rodata_sh0 mm /\ rclean mm RSTK /\ rclean mm RBstdout
    /\ rclean mm RSTG                                                      
    /\ (exists errv, rw_cells bsegs mm (errno_addr (Z_to_bv 64 ATP)) [C4 errv])
    /\ stdout_file mm so.

  Lemma geo : ATOP <= ALO /\ ALO + 8388608 - 4096 = usp /\ KHIGH <= ALO /\ usp + 24 <= 2^47 /\ usp mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"] "h04__x1h14__x2h21Hh37__arithh44__ffh57__sat17h67__sat18h77__sat19h88__varmaph95__with:4__p1h;2Hah<4__x3p;1p;2p;3p;4p;7p;8p;6g01WDj1kTg006mj10Tg00:Lj18Tg00_Tj2>Tg00<Hj22Tg00:0j21Tg00Jaj3?Tg00dcj14Tg00_7j2jTg01?Gj2gTg00@Tj27Tg01X:j1dTg01Y8j2aTg00@8j2QTg01Y`j3^Tg01ZDj2]Tg00;hj1\Tg00C@j1[Tg00C`j2ITg00D>j1ZTg00D\j4ATg00E:j1YTg00EXj1XTg00FCj2BTg00HWj1WTg01[5j3FTg00I9j2UTg00I[j2TTg00J5j2STg00K;j3iTg00KZj4hTg00Ffj4JTg00?Yj1CTg00b<j2@Tg00cNj3DTg00d7j2OTg00N`j3KTg007Rj1eTg01KCj3cTg00GQj2LTg00MPj4ETg00H4j3bTg00Qfj7PTg00Rnj8fTg015Fj6`Tg00RJj7_Tf0R0#0#0p==%00#0#0#0#0#0#0#0p=<%40#4#4#4p=3%00#0#0#0p=G%40#4p=Vg00U<R1g00X]R27?0p=H1120p=91L10p=:f1R3=b10p=;f2R4g00V9R5g00VXR6P6g00W8R7P1P3g00ZjP0CJg00WXR8FPp=5f3R9P5P6P6P7P4P3P0Gfp=6P3P5P6P6P7P0P8FPp=RP3P5P6P6P7P0E`p=NP4P5P6P6P7P3P0F_p=Mp,2rcR5#kR8p,3uspR:g00X8R;#0R<#0R=#=R>#<R?#0R@#=#<#8RA'>%8?R?'2RB'112BA/>?=?1:RC%3@#3#3#3#0#=#G#<#8R@/1BRB%4;RD#0#=#8RE,2:%8<RF%4<RG#4#VRH#8RI'jRJ'1RK%8>R>,g:RL#HRM'7RN'7RO'7%d5R5%4D#3#3#3RP#0#3#3#0#=#G#<#<#8RQ/18%4P#3#3#0#=#G#<#<#8,18RP'7RR1aFIRS1Q2F%9I1Q2J[[RT%9FRUg01[XRVA^FI3UW;RI%9J\V^;URU1]:>RV%9:%9>RW%9L[[RXg00Z>RY#\RZ%[YR[P11I14R\P3%Z1R]CA%Y1R^%X1R_1B1;R;%:AR`';1B1<R<55_%W6R6AF1<`%:?R<';95_;C61U_7R7P0P4g00\8Rag00\XRb'T1S04=?abdAi123ChRbb4b8b9X01X11120A/131>4A/2?Ra,13[^01^11P0P:P8p,5USPLORcO3b3b5b6b7b2PCPOP5PRPSPTPIPUPVPXPZP[1I13ROP^P1AF1;`/;<RC/;`=F1<g01\4R<P;CJ,R_P7Pbb4b8b9X011>0A/2?/2A/>?=?10^01P0P:O1b3b5b6b7b2PBPNP5PRPSPTPIPUPVPXp-0RBg00Y;Rd#CRe#CRf,@1Rg1@1e1@1d5D15D1g00ilRd'O=KYZP[P1P1P\P4P]CAP3P]CAP^P_%:QR\1B1=R=55_f4Re,N_5M_P6P_1;=`=5_;P6%:@=5_CC6C6P7Pbb4b8b9X01X11W:11Q3/74124A/1311@a[[^01^11^:BP0PPP8P:PePcO5b3b5b6b7b2PKPMP5PRPSPTPIPUPVPXPZP[POP^P_%:E,;;%:F%eH5c155_RHP6PHC6P7Pbb4b8b9X01120E/1J123E/1J[^01P0P:p,5USPHIO2b3b5b6b7b2P5PRPSPTPIPUPVPX%CfRf#C,@11@1f=D1g5D1/Od=KYZP[P1P]P3P11I19P4P]CACAP^P_P_1L12R21B1DRD55_P6P_%:>95_2P6A5_2;C6C6P6P_1B1GRG95_\f5,N_5M_P6P_1;G`=5_DP6P_P1P;P<P2CJ,R_R_P6P_C6C6C6C6P7Pbb4b8b9X01X11X<1X:B%93%94\W[11Q9/7e12eA/19%H9%He[[[[^01^11^<1^:BP0PPP8P:PLP3PePcp,5USP16O8b3b5b6b7b2CECECECEg01\[Rc,1812cA/>?=?1:g01]P/1c/7N'7'7eo"). Qed.

  Lemma errno_addr_ATP : errno_addr (Z_to_bv 64 ATP) = 0x5ed1ec.
Proof.
vm_compute. reflexivity. Qed.

  
  Section AfterCallee.
    Variables (LB : list ablock) (m m' : amem).
    Hypothesis HP : aheap_pres CI LB (usp + -128) m m'.
    Hypothesis HS : astk_shadow_pres (usp + -128) m m'.
    Hypothesis HLB : forall b, In b LB -> 0x60f000 <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.

    Let AG : magree bsegs (dcli CI LB (usp + -128)) m m' := magree_of_dpost _ _ _ _ _ HP HS.

    Lemma ci_drv : forall lo' hi' a, In (lo', hi') drv_img_ranges -> lo' <= a < hi' -> dcli CI LB (usp + -128) a.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"; "AfterCallee"] "h02Hah14__x1h24__x2h34__x3h41Hh53Hinh67__arithh74__ffh87__sat17h97__sat18h:7__sat19h;8__varmaph<5__with=1ah>2a'h?3hi'h@2ivhA3lo'p;2p;4p;3p;1p;5p;7p;8g00]8j2hTg00^Wj4GTg01^Fj3=Tg00@8j22Tg01^]j2ZTg006mj10Tg01@_j1UTg00<Hj2RTg01_Yj5LTg01WDj1JTg01ISj1>Tg00:Lj16Tg00_7j2bTg01`^j2ETg01aXj2XTg01bQj2WTg0104j29Tg00Jaj3CTg00@Tj2;Tg00m@j2VTg01cIj3BTg01cfj3ATg01X:j1TTg00dcj14Tg00:0j2:Tg01Y8j2QTg01Y`j3KTg01ZDj2MTg01?Gj2NTg00;hj1OTg00C@j1PTg00C`j2?Tg00D\j4ITg00E:j1STg00EXj1gTg00FCj2<Tg00Ffj4HTg00RJj7fTg00HWj1eTg00Rnj8aTg00I9j2\Tg00I[j2[Tg00J5j2YTg00K;j3]Tg00KZj4^Tg00MPj4_Tg010Nj4`Tg01dCj3DTg01d]j3cTg00Qfj7dTf2R0f1R1':f0R2';p=1%02#0p=8%42#4#4#4p=3%02#0#0#0p=@%02#0#0#0#0#0#0#0p=7g00X]R3/:2p=5P1g00V9R4g00VXR5P5g00W8R6P2g00WXFdp=Fg00U<R71h77R8P7P7P0P1CGg01e73=f3R91210R:711p,2rcR;p,2AI,Z;R<p,2LBR=p,3uspR>g00X8R?#0R@#0#8RA#0#8#U'RRBP0DL%J;RC#>%>B,20710%6@RD%3@#6RE'bRF,2091B01E<0RB1X=0122F91C21E<21W=2'9'9%>29C79';X>7,V7'9R='9P8A=82<AB772AA772,29719';X@8P7P7f4P9CGRGA=8G<AB77GAA77G,20710R<p,6DRV_CIPGP1O2%T;%4?R;#4#3#3#3RG#0#3#3#0#8#@#7#7#6%4G#3#3#0#8#@#7#7#6,:C71C1QDE123D%5E123F[[%5DRCg01[XRGAKDE1UW0%5F\G^0C%6ARA,M>%5>%5A1N>A#5[[g00Z>RA#O%PAP71?70P11?79CI%S7%g7RAP4P5P5P6PAP4P5P5P6P71<7?g00Zj1<7@R@CH,FAP7P@g00[Q1<7;CH,FAFfR;%e5P;Ga1\A6P2P0g00\8RAg00\XR6'[1Y20=CA6dA]731C^b7b;b<X17X27X37A121:12099110[^17^27^37P2f8f7f9f5O4b6b8b9b:b4P<eC_C`9DB=3c3DW0W5X=7X?7WAo"). Qed.
    Lemma ci_drv_sh : forall lo' hi' a, In (lo', hi') drv_img_ranges -> shad lo' <= a < shad hi' -> lo' mod 8 = 0 -> hi' mod 8 = 0 -> dcli CI LB (usp + -128) a.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"; "AfterCallee"] "h02Hah14__x1h24__x2h34__x3h44__x4h54__x5h64__x6h74__x7h81zh91Hh:2H0h;2H1h<3H10h=3H11h>3H12h?3H13h@3H14hA2H2hB2H3hC2H4hD2H5hE2H6hF2H7hG2H8hH2H9hI3HinhJ2M1hK2M2hL7__arithhM4__ffhN7__sat17hO7__sat18hP8__varmaphQ5__withR1ahS2a'hT3hi'hU2ivhV3lo'hW1qhX2q0hY2q1hZ1rh[2r0h\2r1p&0p;2p;4p;3p;1p;5p;6p;7p;8g00]8k20@Tg00^Wj4kTg01^Fj3TTg01ISj1:Tg006mj10Tg00:Lj1=Tg01?Gj22Tg01^]j2nTg01@_j1\Tg00<Hj27Tg01_Yk50?Tg01WDk10=Tg00_7k206Tg01`^j2XTg01aXk202Tg01bQj2bTg0104j2CTg00@Tj29Tg00m@j2vTg00_Tj2MTg00`Qj2;Tg01cIj3gTg01cfj3dTg01f>j24Tg01f[j1qTg013kj6iTg01gTj2YTg01h5j1]Tg01hNj2RTg00@8j23Tg01i5j2PTg00:0j2@Tg01i\j2UTg01jBj2[Tg01X:k10>Tg00dcj15Tg01Y8k20;Tg01Y`k30:Tg01jhk205Tg00?Yj1GTg00b<j2ETg01kIj3fTg00aSk204Tg00bek303Tg00d7j2cTg01l2k201Tg00;hj1|Tg00N`j3aTg00C@j1{Tg00D>j1zTg00C`j2NTg00E:j1yTg00EXj1xTg00GQj2VTg01l^j6wTg00HWj1uTg00eHj3STg00H4j3LTg00FCj2`Tg00Ffj4HTg01[5j3tTg00I9j2sTg00I[j2}Tg00J5j2~Tg00Jaj3WTg00K;j3rTg00KZk400Tg00MPj4^Tg010Nj4eTg01dCj3hTg01d]j3OTg01mBj1pTg01nFk407Tg00cNj3oTg00D\k408Tg00Qfk709Tg00Rnj8mTg00RJj7lTf3R0f2R1'@f1R2f0R3'3'9p=1%03#0p=Ig00U<R4g00X]R57W3p=?%53#5p=jAW423p=61@53p=B1323,91p=Q%53#5#5#5p=>%03#0#0#0p=Z%03#0#0#0#0#0#0#0p=K1@12/93p>0<Ao423p=FP4P1P2P3H08p=<P4P2g01\4P3CHp=JP2g00V9R6g00VXR7P7g00W8R8P3g00WXK09p=81`43p=DP0P6P7P7P8P1P2P3Gmp=AP1P6P7P7P8P2P3Flp=_20@44R9P4P4P1P2Ckg01e73T%:0P2P2%:1C1f4R:g00X8R;#0R<#IR=#=R>'2#?R?p,2rcR@p,2AI,n@RAp,2LBRBp,3uspRC%0=R=#0#I#\'7RDP:I0?&0=@RE#:P:P:%:DC1PDP:P:%=<RD%j<RF#j#=RG+06RHC11XA:RI202B:RJPEP3P3PHC11XA31bB3'C'Cf5RK%:3'6'9XS4RL,v4RM'CRN'CP4PLg01nbRL,M:,;>ROPEPOPOPHC1RP1XAORQ1bBORB'CRR'C%:ORS,6:P9AT93AAg4431MKL,;>RTPTAd443C1'9XU9P4P4f6RTPKCkRUAT9UAAg44UPOPOAd44UC1ROp,6DRV_CIPUP0O2P4%:TRUP3PKPKPUC1X84P114T>,7LRA%qTR9EiPAP:P:%:KC1P4PUf8RU/4>,7LPTPTP3C1X84P3PAP9Eif7R9/4>,7LPKPKPAC11YU>%?>RA#]RVf9RW14W>,;>12W>'7'6[1RW>135>RWf:RX/2>RY#B?QY>[1PX>13>5RXf;RY/2>RZ,3>1@Z5'9[1UY>f<RZ/4>#?\A1[Z>f=R[/2>/6[\A14[>P4f>R[/2>P41Y[>f?R[14[>,;>12[>'7'6\V1R[>f@R[/2>RV#B?QV>\W1P[>fAR[/2>RW,3>1@W5'9\X1U[>fBRX/4>#?\A1[X>fCRW/2>/6W\A14W>P4fD/2>P4%==R=,YC%?=RV#]14C=R\,;=12C=R]'7,6C[1RC=135=%B]?Q]=[1PC=13=513=]1@]5'9[1UC=%?\\V1[C=16]C\VP\P4P]P4&0>@%5;R@#5R]#>#>#>R\#0#>#>#0#I#Z#K#K#=%5\R\#>#>#0#I#Z#K#K#=,@E80<E20;DG135D%BG135H[[%BDREg01[XRVB0:DG2UW0%BH\V^0Eg00Z>RE%\;-054RVg00Y;RH#GRG#G#GRD#GRC#GR=#G,E45f41E4C9f4V2044>1E4G60341E4HRH'F'F'Fg00ilRG'c1E4=1E4DRD/FH'F1FHD/cG+01%|E5aE3a%{E%z4RE1N4K7<91N499<E97<11N4T9<E91N4:?<9E7<07<2%y4%x4REPEPEP6P7P7P81V4>R61V45RG'J,8EEwRD%u7R7%D@RH%0@R@#0#DR=9S46%0]#DR]5L4'J,8ECAP7PEPEPDP71`4;R;%DFRF9S46%5@#DR@5L4'J,8ECAP7PE1J]G,8EP7PE1J@G,8EP7PEP4%0\#I#Z#K#=R\,V4R@=L4Fg00ZjRF%D<R<CH,8EP4P<g00[QRGAL4@=CH,8E5_EP7P4P;PFAt4<@9S46R6CH,8EP4P6PGPHCH,8E5_ECACACACACA1sE8P3P1g00\8REg00\XR8'}1~31=WE8dAr452H00bMbPbQX14X24X34X44X54X64X74g01o\\ARA1;>K/79R5,60[1615\A%?URA17\9PKPK17\UC1PK1MT\,;>R\P\P9C1[\A[[[^14^24^34^44^54^64^74P3PYPXPZPWfPfOfQP[fHfKfLfIO<bLbNbOb@b\bYb?b>b=b<bHb[bXbGbFbEbDbCbZbWbBbAb;b:b9PU1MTL,;>R>P>P9C1eb0b0POeC^Ce9hQB9OPRP4PSP:%p:H07C^Ce9OJM9OIN3O3hXK?WJW0WIXR4XT4XV4o"). Qed.
    Lemma ci_drv_sh' : forall lo' hi' a, In (lo', hi') drv_img_ranges -> shad lo' <= a <= shad (hi' - 1) -> lo' mod 8 = 0 -> dcli CI LB (usp + -128) a.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"; "AfterCallee"] "h02Hah14__p1h24__x1h34__x2h44__x3h54__x4h64__x5h74__x6h84__x7h91zh:1Hh;2H0h<2H1h=3H10h>3H11h?3H12h@3H13hA3H14hB2H2hC2H3hD2H4hE2H5hF2H6hG2H7hH2H8hI2H9hJ3HinhK2M1hL7__arithhM4__ffhN7__sat17hO7__sat18hP8__varmaphQ5__withR1ahS2a'hT3hi'hU2ivhV3lo'hW1qhX2q0hY2q1hZ1rh[2r0h\2r1p&0p;2p;4p;3p;1p;5p;6p;7p;8g00]8k20ATg00^Wj4oTg01^Fj3XTg01ISj1:Tg00:Lj1=Tg00_Tj21Tg00:0j24Tg006mj10Tg01?Gj22Tg01^]j2qTg01@_j1pTg00<Hj26Tg01_Yk50?Tg01WDk10=Tg00_7k206Tg01`^j2[Tg01aXk202Tg01bQj2dTg0104j2GTg00@Tj2@Tg00m@j2zTg00`Qj2>Tg01cIj3bTg01cfj3kTg01f>j25Tg01f[j1mTg013kj6aTg01gTj2VTg01h5j1`Tg01hNj2UTg00@8j23Tg01i5j2TTg01i\j2^Tg01jBj2]Tg01X:k10@Tg00dcj19Tg01Y8k20>Tg01Y`k30<Tg00?Yj1ETg00b<j2HTg01jhk20;Tg01kIk30:Tg00d7j2jTg01l2j2iTg00;hk107Tg00N`j3fTg00C@k105Tg00D>k104Tg00C`j2PTg00E:k103Tg00EXk101Tg00GQj2RTg00Ffj4LTg00HWj1}Tg015Fj6|Tg01l^j6{Tg01[5j3cTg00eHj3YTg00H4j3MTg00FCj2nTg00I9j2yTg00I[j2~Tg00J5j2xTg00Jaj3ZTg00K;k300Tg00KZj4wTg00MPj4eTg010Nj4gTg01dCj3lTg01d]j3QTg01mBj1vTg01nFj4uTg00cNk308Tg00D\k409Tg00Qfj7tTg00RJj7sTg00Rnj8rTf2R0f1R1'4f0R2'@p=A%02#0p=Jg00U<R3g00X]R47Z2p=Bf3R5/401312'@p=<%92#9p=hAZ312p=81442p=?1312,@0p=S1412,@0p=_%92#9#9#9p=C%02#0#0#0p=\%02#0#0#0#0#0#0#0p=KB08312p=IP3P0P1P2H09p=DP1g00V9R6g00VXR7P7g00W8R8P2g00WXFtp=71n32p=FP3P1g00ZjP2CLp=OP0P6P7P7P8P1P2Fsp=WP5P6P7P7P8P0P1P2Grp=;P3P1g01\4P2CLp=N20A33R9P3P3P0P1Cog01e73X%:5g00X8R:#=R;,10#:,417A1f4R<%0:R=#JR>#=R?'2#Bp,2rcR@p,2AI,q@RAp,2LBRBp,3uspRC%0>R>#0#J#p'6RDP5I0?&0=@RE#:P5P5%:DC<PDP5P5%==RD%h=RF#h#=RG+06RHC<1[A5RI202B5RJPEP2P2PHC<1[A21dB2'G'G%:2,8<'@XS3RK,z3RL'GRM'GP3PKg01nbRK,15,>?RNPEPNPNPHC<RO1[ANRP1dBNRB'GRQ'G%:NRR,85P9AX92AAb33211<K,>?RSPSAk332C<'@XU9P3P3f5RSP<CoRTAX9TAAb33TPNPNAk33TC<RNp,6DRV_CIPTP0O2P3%:S11S;RT#:RA,4<9A2<X93P115S?,6KR9%mSEa11<;RU#:,459A95P3PAf7RA/5?,6K14S27ASX93P215T?,6KR9%mTEaf6RT/5?,6K14<97A<1VA?%B?R9#`RVf8RW15W?,>?12W?'6'8[1UW?134?RXf9RY/2?RZ#??SZ?[1TY?13?4RZf:R[/2?R\,3??_\4[1^[?f;R[/5?#B\91][?f<R\/2?/8\\915\?P3f=R]/2?P311];/V?f>/1;R]15]?,>?12]?'6'8\V1U]?f?/1;R]/2?RV#??SV?\X1T]?f@R]/1;RV/2?R^,3??_^4\Z1^V?fARV/1;RZ/5?#B\91]Z?fBRZ/1;R^/2?/8^\915^?P3fCR^/1;/2?P3%=>R>,VC%B>R_#`15C>R`,>>12C>Ra'6,8C[1UC>134>%?a?Sa>[1TC>13>413>a?_a4[1^C>%B`\_1]C>18aC\_P`P3PaP3&0@@%9:R@#9Ra#C#C#CR`#0#C#C#0#J#\#K#K#=%9`R`#C#C#0#J#\#K#K#=,4E7AE20>DG134D%?G134H[[%?DREg01[XR_B0<DG1UW0%?H\_^0Ep-0REg00Z>R_g00Y;RH#E#ERG#ERD#ERC#ER>#E,H3%p:-0;31H3>60:31H3HRH'I'I1H3G,IHg00ilRG'j'i1H3C1H3DRD/IH'I1IHD/jG'i&07_5f_3f&05_&043R_1P3S7DA1P3A9D_A7D01P3T9D_A1P3<?DA_7D57D1&033&013R_P_P31R34R<g00[QRG1R3?RDCL,7_%}7RH%0a#FRa,O<,7_P_P6P7P7P8PYE|5W_C;PHP_P_P_P6P7P7P81ND<,7_E{R7PH%F@R61R3;5c3%0@R@#0#FR;9Y3D=M3a'N,7_C;PHP_P_P7PH1n3:R:%FFRF9Y3D%9@#FR@5M3'N,7_C;PHP_1N@<,7_PHP_%0`#J#\#K#=R`,R3R@=M3F%F=R='O,7_AM3@;,O=,7_5W_PHAc3=@9Y3DRD,O:,7_P3PDPGP6CL,7_5W_C;C;C;C;C;1y_8P2P0g00\8R_g00\XR8'~1x20=Z_8dB00341CwbMbPbQX23X33X43X53X63X73X83W1%?A/@W\Xg01o\\9R91>?T/6WRX,8U[185X\9%BW16`A16`W,4S7ASPS11T`,>?R`P`PAC<[[[[[^23^33^43^53^63^73^83^1EP213[?P[PZP\P^fOfNfPP]PVfHfKfIO=bLbNbObAb\bYb@b?b>b=bIb[bXbHbGbFbEbDbZbWbCbBb<b;b:PA11SK,>?R?P?PTC<eb0b0PNeCeCg9lPB9QOQP3PRP5%v5CuCeCg9QJL9QIM3Q3lWKW0WJXR3XT3XV3o"). Qed.
    Lemma ci_cli_sh : forall lo' hi' a, In (lo', hi') cli_img_ranges -> shad lo' <= a <= shad (hi' - 1) -> lo' mod 8 = 0 -> dcli CI LB (usp + -128) a.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"; "AfterCallee"] "h02Hah14__p1h24__x1h34__x2h44__x3h54__x4h64__x5h74__x6h84__x7h91zh:1Hh;2H0h<2H1h=3H10h>3H11h?3H12h@3H13hA3H14hB2H2hC2H3hD2H4hE2H5hF2H6hG2H7hH2H8hI2H9hJ3HinhK2M1hL7__arithhM4__ffhN7__sat17hO7__sat18hP8__varmaphQ5__withR1ahS2a'hT3hi'hU2ivhV3lo'hW1qhX2q0hY2q1hZ1rh[2r0h\2r1p&0p;2p;4p;3p;1p;5p;6p;7p;8g00]8k20ATg00^Wj4oTg01^Fj3XTg01ISj1:Tg00:Lj1=Tg00_Tj21Tg00:0j24Tg006mj10Tg01?Gj22Tg01^]j2qTg01@_j1pTg00<Hj26Tg01_Yk50?Tg01WDk10=Tg00_7k206Tg01`^j2[Tg01aXk202Tg01bQj2dTg0104j2GTg00@Tj2@Tg00m@j2zTg00`Qj2>Tg01cIj3bTg01cfj3kTg01f>j25Tg01f[j1mTg013kj6aTg01gTj2VTg01h5j1`Tg01hNj2UTg00@8j23Tg01i5j2TTg01i\j2^Tg01jBj2]Tg01X:k10@Tg00dcj19Tg01Y8k20>Tg01Y`k30<Tg00?Yj1ETg00b<j2HTg01jhk20;Tg01kIk30:Tg00d7j2jTg01l2j2iTg00;hk107Tg00N`j3fTg00C@k105Tg00D>k104Tg00C`j2PTg00E:k103Tg00EXk101Tg00GQj2RTg00Ffj4LTg00HWj1}Tg015Fj6|Tg01l^j6{Tg01[5j3cTg00eHj3YTg00H4j3MTg00FCj2nTg00I9j2yTg00I[j2~Tg00J5j2xTg00Jaj3ZTg00K;k300Tg00KZj4wTg00MPj4eTg010Nj4gTg01dCj3lTg01d]j3QTg01mBj1vTg01nFj4uTg00cNk308Tg00D\k409Tg00Qfj7tTg00RJj7sTg00Rnj8rTf2R0f1R1'4f0R2'@p=A%02#0p=Jg00U<R3g00X]R47Z2p=Bf3R5/401312'@p=<%92#9p=hAZ312p=81442p=?1312,@0p=S1412,@0p=_%92#9#9#9p=C%02#0#0#0p=\%02#0#0#0#0#0#0#0p=KB08312p=IP3P0P1P2H09p=DP1g00V9R6g00VXR7P7g00W8R8P2g00WXFtp=71n32p=FP3P1g00ZjP2CLp=OP0P6P7P7P8P1P2Fsp=WP5P6P7P7P8P0P1P2Grp=;P3P1g01\4P2CLp=N20A33R9P3P3P0P1Cog02093X%:5g00X8R:#=R;,10#:,417A1f4R<%0:R=#JR>#=R?'2#Bp,2rcR@p,2AI,q@RAp,2LBRBp,3uspRC%0>R>#0#J#p'6RDP5I0?&0=@RE#:P5P5%:DC<PDP5P5%==RD%h=RF#h#=RG+06RHC<1[A5RI202B5RJPEP2P2PHC<1[A21dB2'G'G%:2,8<'@XS3RK,z3RL'GRM'GP3PKg01nbRK,15,>?RNPEPNPNPHC<RO1[ANRP1dBNRB'GRQ'G%:NRR,85P9AX92AAb33211<K,>?RSPSAk332C<'@XU9P3P3f5RSP<CoRTAX9TAAb33TPNPNAk33TC<RNp,6CLI_CIPTP0O2P3%:S11S;RT#:RA,4<9A2<X93P115S?,6KR9%mSEa11<;RU#:,459A95P3PAf7RA/5?,6K14S27ASX93P215T?,6KR9%mTEaf6RT/5?,6K14<97A<1VA?%B?R9#`RVf8RW15W?,>?12W?'6'8[1UW?134?RXf9RY/2?RZ#??SZ?[1TY?13?4RZf:R[/2?R\,3??_\4[1^[?f;R[/5?#B\91][?f<R\/2?/8\\915\?P3f=R]/2?P311];/V?f>/1;R]15]?,>?12]?'6'8\V1U]?f?/1;R]/2?RV#??SV?\X1T]?f@R]/1;RV/2?R^,3??_^4\Z1^V?fARV/1;RZ/5?#B\91]Z?fBRZ/1;R^/2?/8^\915^?P3fCR^/1;/2?P3%=>R>,VC%B>R_#`15C>R`,>>12C>Ra'6,8C[1UC>134>%?a?Sa>[1TC>13>413>a?_a4[1^C>%B`\_1]C>18aC\_P`P3PaP3&0@@%9:R@#9Ra#C#C#CR`#0#C#C#0#J#\#K#K#=%9`R`#C#C#0#J#\#K#K#=,4E7AE20>DG134D%?G134H[[%?DREg01[XR_B0<DG1UW0%?H\_^0Ep-0REg00Z>R_g00Y;RH#E#ERG#ERD#ERC#ER>#E,H3%p:-0;31H3>60:31H3HRH'I'I1H3G,IHg00ilRG'j'i1H3C1H3DRD/IH'I1IHD/jG'i&07_5f_3f&05_&043R_1P3S7DA1P3A9D_A7D01P3T9D_A1P3<?DA_7D57D1&033&013R_P_P31R34R<g00[QRG1R3?RDCL,7_%}7RH%0a#FRa,O<,7_P_P6P7P7P8PYE|5W_C;PHP_P_P_P6P7P7P81ND<,7_E{R7PH%F@R61R3;5c3%0@R@#0#FR;9Y3D=M3a'N,7_C;PHP_P_P7PH1n3:R:%FFRF9Y3D%9@#FR@5M3'N,7_C;PHP_1N@<,7_PHP_%0`#J#\#K#=R`,R3R@=M3F%F=R='O,7_AM3@;,O=,7_5W_PHAc3=@9Y3DRD,O:,7_P3PDPGP6CL,7_5W_C;C;C;C;C;1y_8P2P0g00\8R_g00\XR8'~1x20=Z_8dB00341CwbMbPbQX23X33X43X53X63X73X83W1%?A/@W\Xg01o\\9R91>?T/6WRX,8U[185X\9%BW16`A16`W,4S7ASPS11T`,>?R`P`PAC<[[[[[^23^33^43^53^63^73^83^1EP213[?P[PZP\P^fOfNfPP]PVfHfKfIO=bLbNbObAb\bYb@b?b>b=bIb[bXbHbGbFbEbDbZbWbCbBb<b;b:PA11SK,>?R?P?PTC<eb0b0PNeCeCg9lPB9QOQP3PRP5%v5CuCeCg9QJL9QIM3Q3lWKW0WJXR3XT3XV3o"). Qed.
    Lemma stack_dcli : forall a, usp + -128 <= a < 2^47 -> dcli CI LB (usp + -128) a.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"; "AfterCallee"] "h02Hah14__x1h24__x2h31Hh47__arithh54__ffh67__sat17h77__sat18h87__sat19h98__varmaph:5__with;1ah<2a'p;1p;2p;5p;3p;4p;7p;8g006mj10Tg01@_j1TTg00<Hj2;Tg00:0j21Tg00:Lj17Tg00_7j2STg00@8j26Tg00@Tj22Tg01^]j2HTg01_Yj5FTg01WDj1ETg01ISj1<Tg01`^j2ATg01aXj2aTg01bQj2[Tg0104j2:Tg00Jaj3?Tg00m@j2XTg01X:j1WTg00dcj14Tg01Y8j2RTg01Y`j3QTg01ZDj2ITg01?Gj2JTg00;hj1KTg00C@j1GTg00C`j2LTg00D>j1MTg00D\j4NTg00E:j1OTg00EXj1PTg00FCj2=Tg00GQj2BTg00H4j3UTg00Ffj4DTg007Rj1eTg01KCj3dTg00RJj7cTg00HWj1bTg00Rnj8`Tg00I9j2_Tg00I[j2\Tg00J5j2ZTg00K;j3]Tg00KZj4^Tg01dCj3@Tg00Qfj7YTf0R0#0#0p=9%40#4#4#4p=3%40#4p=V%00#0#0#0p=>%00#0#0#0#0#0#0#0p=8g00X]R1/10p=5f1R2g00V9R3g00VXR4P4g00W8R5P0g00WXFYp=Cg00U<R6p,3uspR7g00X8R8#0R9#0#9R:#0#9#TR;';R</10%79R=%39R>#7R?'SR@,60RA'2p,2rcRBp,2AI,HBRCp,2LBRDP<P2DF%EBRE#</12%<<,62'211<2162@R<'21AC21aD211E0/2A1AC01[D0':':f2RD%<05?6'2X<6,X6':':%WB%V8#3#3#3RB#0#3#3#0#9#>#8#8#7/1E%4B#3#3#0#9#>#8#8#7,1E'21R=?161=%5?161@[[%5=REg01[XRBAQ=?2UW0%5@\B^0E%7:R:,I7%57%5:1J7:#5[[g00Z>R:#K%G:P61L6DP2%M6CN%O6%P6R:P3P4P4P5P:P3P4P4P5P61=681B6;5U6g00Zj1=69R9CD,C:P6P9g00[Q1B6=%e>5d6CD,C:FcR>%b4P>G`1_:5P0PDg00\8R:g00\XR5'\1Z0D=?:5dA]612C^b5b9b:X16X261;0;/12/2<1;2;/1D16D@'2[^16^26P0f6P7f5O3b4b6b7b8b33@3@W0W;o"). Qed.
    Lemma stack_sh_dcli : forall RLO RHI a, ATOP <= RLO -> RHI <= KEND -> shad RLO <= a < shad RHI -> dcli CI LB (usp + -128) a.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"; "AfterCallee"] "h02Hah14__p1h24__p2h34__x1h44__x2h54__x3h64__x4h74__x5h84__x6h91zh:2GEh;1Hh<2H0h=7__arithh>4__ffh?4__p3h@8__varmaphA5__withB5__x10hC4__x7hD4__x8hE4__x9hF2H1hG3H10hH3H11hI3H12hJ3H13hK3H14hL3H15hM3H16hN3H17hO3H18hP3H19hQ2H2hR3H20hS3H21hT2H3hU2H4hV2H5hW2H6hX2H7hY2H8hZ2H9h[2LTh\3RHIh]3RLOh^7__sat17h_7__sat18h`7__sat19ha7__sat22hb7__sat23hc1ahd2a'he1ohf1qhg2q0hh2q1hi2q2hj1rhk2r0hl2r1hm2r2p%0p&0p;1p;2p;5p;3p;4p;6p;7p;8g01WDk10LTg00:0j21Tg01ISj1CTg006mj10Tg01@_j1pTg00<Hj23Tg021@k207Tg00@8j22Tg0104R0j2ITg01^]j2xTg021ej5tTg01_Yk50KTg01TGk30HTg01X:k10GTg00dcj15Tg00:Lj1DTg01Y8k208Tg00_7k206Tg01Y`k305Tg01ZDk203Tg01?Gj28Tg00?Yj1:Tg00b<j2nTg00d7j2dTg00;hj1wTg00N`j3gTg00C@j1uTg00D>j1sTg00E:k10JTg00EXk10ITg00HWk10FTg00FCj2qTg00I9k20BTg00I[k20ATg00J5k20@Tg00Jaj3]Tg00K;k30>Tg00KZk40=Tg01d]j3ZTg01`^j2aTg01aXk20<Tg01bQj2oTg00@Tj2@Tg00m@k20;Tg00_Tj2_Tg00`Qj2>Tg01f>j2=Tg01f[j1lTg013kj6^Tg01gTj2UTg01h5j1kTg01hNj2YTg01i5j2XTg01i\j2WTg01jBj2VTg01jhk204Tg01kIj3\Tg00aSk202Tg00bej3[Tg01l2k201Tg00GQj2hTg00eHj3TTg01[5k300Tg007Rj1~Tg01KCk30:Tg01dCj3mTg01mBj1}Tg01nFj4|Tg00MPj4{Tg010Nj4zTg00cNj3bTg00C`k20?Tg00D\j4yTg00Ffj4eTg00Qfj7rTg015Fk60CTg00RJk70DTg00H4k30ETg00Rnj8fTg01l^j6vTf3R1f2R2'1f1R3f0R4'2'@p=6%04#0p=Q%54#5#5#5p=L%04#0#0#0p=c%04#0#0#0#0#0#0#0p=B1123/@4p=`%54#5p>09g00X]R5/14p=<g00U<R6/n4p=?Ab6349b62p=O20?64p=GP6P2P3P4Cyp=71h64p=F1q64p=9P2g00V9R7g00VXR8P8g00W8R9P6P3g00ZjP4Ceg00WXR:Frp=AP3P7P8P8P9P4J0Cp=SP2P7P8P8P9P3P4K0Dp=JP6P3g00[QP4Cep=RP3P7P8P8P9P4P:Frp=;B0E634p=EP1P7P8P8P9P2P3P4Gfp=Nf6R:P7P8P8P9f5R;f4R<P1P7P8P8P9P2P3P4GfGfp=KA]634p=4A]645p=H1234,@2p=PAb634p=iP6P3g01\4P4Cep=MP3P7P8P8P9P4Evp=jp,2rcR7$0LR=/12g022[,12%C<P2P2%C1C6p,3uspR>g00X8R?#0R@#QRA#0RB#0#QRC#pRD'3RE#CRF-071121F11F1'IP012<F11F<P7p,2AI,x7R0p,2LBRGPEP;DtP412;FP7P0PGPEP:I0KRH%C=RIP:P:PFC6RJf8RK>0H=;%CKRL,1I&0G7S00%5?R7#5RM#L#L#LRN#0#L#L#0#Q#c#B#B#DRO%5NRN#L#L#0#Q#c#B#B#D,1=RP7`=RQ%D@RR%5@RS#5$09RT#DRU+08RV125R%<U206RURW,25[[RX%<RRYg01[XRZB05RU3UW0RU%<W\Z^0YRY%DBRZ-03>%<>%<Z18>ZR[#<R\[[p-0R]g00Z>R^g00Y;R_#:R`#:Ra#:Rb#:Rc#?Rd%?aRa1n6_R_3Og00ilRe'd%w^Rf3g%u^Rg%G;Rh%s6Ri77:%G:Rj97i<772%G1773&0J6S01&0I6Rk%FO%9ARl5Ak1SkK5Jk&0F8R8Pk1q6?Rm%0M#9RM5AkP8Pk%9@R@%97'R,;kRnP8PkAAkM@f9Ro,Sk5JkP8Pk%BC#BRC#DRp#FRq,El%07R7#95AkP8AAkm@=JknCNFKFK20Bk9S02P4P2g00\8R9g00\XRn+0A20@42=]9ndB0>653H0=S03b>b@bAX36X46X56X66X76X86X1]W2A`O<:113:121<f:RO9`K<13KpRpf7Rn'1P;P:P:PnC6[[[[[^36^46^56^66^76^86^1]^2]P4f<R9f=Rr#C'2PPf>RP#CP=P>PFP9PIP<P;P:Pop,5USPLOS04O=b=b^b_b`b<b;3ZW[P4O111F;PEP:P:PWC61a0:RI20<G:RsP=P4P4PWC61a041oG4'I'I%C4,4n'@Xd6Rt-0;6Ru'IRv'IP6Pt%DARtg01nbRw,_:'>RxP=PxPxPWC6Ry1a0x1oGx'IRG'I%CxS05,4:P6PF114nX96P41=EtRF,3wRx%lEE^11x:P6%CoRxP4PKPKPxC6X96P<1=ot,3wR0%loRzE^P0PnPnPLC6P6Pxf;Rx/=t,3wPoPoP4C6X96P4P0PzE^1=Ot,3wPKPKP0C61UEt%HtR0#kRz1>tF18EtRL'3,4E[1YEt125tR{%<L?PLt[1XEt12t5R|12tL11L5'@[1WEt%HF\01VEt14LE\0PFP6PLP6fBRL/UtfCRF1=Ft,>t18Ft'3'4\z1YFtfDRE/8tR}#<?P}t\{1XEtfERE/8tR},2t11}5'@\|1WEtfFRE/=t#H\01VEtfGRE/8t/4E\01=EtP6fHRE/8tP61UEtfIRE1=Et,>t18Et'3'4\z1YEtfJRz/8tR}#<?P}t\{1XztfKR}/8tR~,2t11~5'@\|1W}tfLR}/=t#H\01V}tfMR}/8t/4}\01=}tP6fNR}/8tP61U>Z%HZR|#k1=>ZR~,>Z/3[,4>[1Y>Z125ZAP\[Z[1X>Z12Z512Z[11[5'@[1W>Z%H~\|1V>Z14[>\|P~P6P[P6Q00PQPVPXPUPY%p?-046R?%:c#:Rc#:RY#:RU#:RX#:RV#?5\6%?Y%?cRc%?`R`9\6?'i3O2026tRY=[6_%:V#?A[6Yc%?bRb1ia`3O3O/de+01%?X%?U9\6?A[6Yd?Ob_3O/de=g^f5g^Pg%Go?7<i?7Oj%GK97hO772%GO?7Oi%Gn771?7Oi773Q01PkPk%FZR31h65R5'M,;k,jkP8%9SRi%5A#99T63/El'M,;kCNP8PkPk%FtR3,R5,;kRAP8%9BRB9Ak51Sk95JkCNP8PkPk1M35,;k,jkR2P8%0S#9RS%07#9Rh9T63/EB'M,;kCNP8PkPkPAP81Skr1RM3,;k5JkCNP8PkPkP2P8%FD,Ei%57#9R79T63/EM'M,;kCNP8Pk%0N#Q#c#B#DRN#FRM/E7=Ak@P8Pk1SkP1EMh,R@,;k5JkP8Pk%BC#B#B#DRC#F9AkSP8Pk1Emq=AkiP8Pk1Ml5,;kP8B006@M9T63R39Akm%FR%~T60:6,R3,;k5JkFKFKFKFKFKQ02Q03b>b@bAX36X46X56X66X76X86XC6XD6XE6XB6X1]X2]X?]g01o\Rk\|1>ZO/3<,41[%<O/@9\{Pk\0R01>tK/3x,4n[f?12xtRK'@\{13nD1>tx/39'4\013NxR0/1:APLn011xC11pO%H9PO1_xN,>tRpPpPWC6[[[[[[[[[[^36^46^56^66^76^86^C6^D6^E6^B6^1]^2]^?]P413NFfYRN'1%<EPKP;PxPEPzP9fZP<P>PNP=POf@fAP}fOfRfPfWQ04p,5USP16OGb=babbbSbmbibRbPbObNbMblbhbLbKbJbIbHbkbgbGbZbYbXbWbjbfbVbUbTb<b;P=1_ow,>tRtPtPWC6eb0b0b:9myGP6Q05P:%}:C|C{Cz9Zsu9ZIv3Z9mHJW:P4O1n200100000021100011000beW0WQWFXc6X\6X]6o"). Qed.

    Lemma ABASE_after_dpost : forall L RNG st LB' so, AHEAP AI L RNG st LB' m' -> mem_inv bsegs m' -> stk bsegs m' ALO (usp + -128) ->
      ABASE so m -> ABASE so m'.
Proof.
intros L RNG st LB' so AH' MI' ST' (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF).
pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof RSTK_rlo as RSC. atop_facts. unfold KHIGH in G3.
split; [exact ST'|]. split; [exact MI'|].
split. { unfold AMFRAME in *. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply stack_dcli; cbn in Ha; lia]. }
split. { eapply ASTAT_agree; [exact AG| | exact AS]. intros a [Ha|Ha].
- unfold astat_app in Ha. left. right; left.
Ltac tryr lo hi := exists (lo, hi); split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto | cbn; lia].
Ltac drv_pick k := let L := eval vm_compute in drv_img_ranges in
  let rec go L := lazymatch L with
    | cons (?lo, ?hi) ?t => first [ k lo hi | go t ]
    | nil => fail
  end in go L.
repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end;
drv_pick ltac:(fun lo hi => tryr lo hi).
- unfold astat_sh in Ha. destruct Ha as [Ha|Ha];
drv_pick ltac:(fun lo hi => apply (ci_drv_sh' lo hi); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity]). }
split. { destruct SE as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
eapply rw_cells_magree; [exact AG| exact Hc|]. intros a Ha. apply (ci_drv RSTDERR (RSTDERR + 232)); [unfold drv_img_ranges; cbn; tauto| cbn in Ha; lia]. }
split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| unfold ssp_guard in Ha; cbn in Ha; lia]). }
split. { eapply atrun_cells0_magree; [exact AG| | exact TR]. intros a [Ha|[Ha|[Ha|Ha]]].
- drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| unfold AINIT_FLAG in Ha; lia]).
- unfold atx_addrA in Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]];
drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| lia]).
- drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| lia]).
- drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| lia]). }
split. { exact ((fun _ => I) CLI_CI). }
split. { eapply rodata_sh0_magree; [exact AG| | exact ROD]. intros a Ha. destruct Ha as [Ha|Ha]; try unfold AHBM_LO, AHBM_HI in Ha;
drv_pick ltac:(fun lo hi => apply (ci_drv_sh lo hi); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div in *; unfold ASHOFF in *; lia| reflexivity| reflexivity]). }
split. { eapply rclean_magree; [exact AG| | exact RCS]. intros a Ha. destruct RCS as [(_ & HL64 & _) _]. unfold hull64 in HL64.
apply (stack_sh_dcli (r_rlo RSTK) (r_rhi RSTK)); [atop_facts; lia| lia| exact Ha]. }
split. { eapply rclean_magree; [exact AG| | exact RCB]. intros a Ha. unfold RBstdout in Ha. cbn [r_rlo r_rhi] in Ha.
drv_pick ltac:(fun lo hi => apply (ci_drv_sh lo hi); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div in *; unfold ASHOFF in *; lia | reflexivity| reflexivity]). }
split. { eapply rclean_magree; [exact AG| | exact RSG]. intros a Ha. unfold RSTG in Ha. cbn [r_rlo r_rhi] in Ha.
drv_pick ltac:(fun lo hi => apply (ci_drv_sh lo hi); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div in *; unfold ASHOFF in *; lia | reflexivity| reflexivity]). }
split. { exists errv. eapply rw_cells_magree; [exact AG| exact ERR|]. intros a' Ha'. rewrite errno_addr_ATP in Ha'. cbn in Ha'.
drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| lia]). }
eapply stdout_file_magree; [exact AG| | exact SOF]. intros a [Ha|Ha].
- apply (ci_drv RSTDOUT (RSTDOUT + 232)); [unfold drv_img_ranges; cbn; tauto| exact Ha].
- drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| cbn in Ha |- *; lia]).
Qed.

    
    Lemma astring_after_dpost : forall P str slack r, astring m P str slack r -> astring m' P str slack r.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"; "AfterCallee"] "h01Hh12Hah24__x1h34__x2h47__arithh54__ffh67__sat17h77__sat18h87__sat19h98__varmaph:5__with;1ah<2ASh=2G1h>1Ph?2_Hh@1rhA5slackhB3strp;1p;5p;2p;4p;3p;7p;6p;;p;8g00C@j1@Tg006mj10Tg007Rj1BTg0080j1gTg01;Cj5ZTg01^]j2VTg01@_j1RTg00<Hj26Tg021ej4Lj5_Tg00:0j21Tg00:Lj12Tg00_7j2fTg00@8j29Tg00@TR0j23Tg01X:j1YTg00dcj17Tg01WDj1UTg01Y8j2TTg01Y`j3QTg01ZDj2PTg01?Gj2OTg00;hj1NTg00C`j2MTg00D>j1KTg00D\j4ITg00E:j1JTg00EXj1HTg00FCj2CTg00GQj2<Tg00H4j3>Tg01KCj3GTg00Ffj4DTg00RJj7STg00HWj1eTg00I9j2dTg00I[j2cTg00J5j2bTg00Jaj3?Tg00K;j3]Tg00KZj4\Tg02=aj2[Tg01ISj1ETg00_Tj2^Tg02I_j6XTg02ZNl;`Tg00Qfj7aTg00Rnj8WTf0R1#0#0p=:%71#7#7#7p=4%01#0#0#0p=A%01#0#0#0#0#0#0#0p=5g00X]R2/11p=8g00U<R3f1R4g00ZjP1CDp==P4g00V9R5g00VXR6P6g00W8R7P1g00WXFap=;f3R8P5P6P6P7f2R9P4P1GWp=F%@3g00X8R:#0R;#:R<#B#g#@g01MRp,1mR=P8P9P4P1DZp,2rcR>p,2AI,V>R?p,2LBR@p,3uspRA%0<R<#0#:RB#RRC'6RDCLP=p,2m'f4P8P9P4p,2AG11D1%2;R=%4;RE#2RF'fRG,91'3%Y>RH%7:RI#7#4#4#4RJ#0#4#4#0#:#A#5#5#2%U>RK'1%7J#4#4#0#:#A#5#5#2,1K'3RJ1T=FRL192=%8F192G[[RM%8=RNg01[XROAQ=F4UW1RF%8G\O^1NRN%2<R<,PARO%8A%8<1OA<R<#8[[RPg00Z>RQ#NRR%@QRQP31M39P4%K3RSCIRT%J3RU%H3RVPVP5P6P6P71C3:R:1<3CR55>31C3;R;'=,;VP3P;g00[Q1<3=%BE5G3RECD,;VFSR=%e6R6P=CF1dV7R7P1P9g00\8R=g00\XRW'c1b19=?=WdA]324C\RWb5b9b:X23X33161C/14194G'3164C/19199G'3[^23^33P1f6R=PAf5RXO3b4b6b7b8b0,[4W1X;3%ED/11%EG,91'3g02TVg01\[RY,1KRZ%0B#ARB#0#:#5R[#2R\,6Y%2B'^=?3Ag01]P/1Y%0I#:#2,6A/1GA?3<2'3'3'3R<'3P0PZP<P>P?P@PDP8D_P1PDPGP=PHPJPLPMPFPNPOPPPRPQPTPUPV1<3\9>3:/=;,;VP6A>3;5,=:,;VCFP7PWb5b9b:X23X33161\/14169C,14[^23^33P1PAPKp,5USPLOO3b4b6b7b8b0PHPJPLPMPFPNPOPPPRPQPSPU%5[#5#5#2R[,<3,=E,;VP7PWb5b9b:11G[P1b4b6b7b8b0g022[,1GePXEXX?<X=ZP4P1O2n2001000000121000000b0W1X;3P1M;`W<W@WAWBX>3o"). Qed.
  End AfterCallee.

  
  Definition WOKb (hi : Z) (iv : Z * Z) : Prop :=
    (ALO <= fst iv /\ snd iv <= hi)
    \/ (fst iv = 0x5ed1ec /\ snd iv = 0x5ed1f0)                                   
    \/ (fst iv = RSTDERR /\ snd iv = RSTDERR + 232)                               
    \/ ablk (fst iv) (snd iv)                                                     
    \/ (ASTAGE <= fst iv /\ snd iv <= ASTAGE + 65536).                           
  
  Definition WOK : Z * Z -> Prop := WOKb (usp + -128).

  
  Lemma WOKb_outside : forall hi W a, ALO <= hi -> Forall (WOKb hi) W ->
    (hi <= a
     \/ (a < 0x60f000 /\ ~ (0x5ed1ec <= a < 0x5ed1f0) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5dc950 <= a < 0x5ec950))
     \/ (0x7fff7000 <= a < 0x10007fff8000)) -> outside W a.
Proof.
pose proof geo as (G1 & G2 & G3 & _). unfold KHIGH in *. atop_facts.
intros hi. induction W as [|[lo1 hi1] W IH]; intros a Hhi HW Ha; cbn; [exact I|].
inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
unfold WOKb, ablk, ASTAGE, AIMG_HI, KLS in H1. cbn [fst snd] in H1.
lia.
Qed.
  Lemma WOK_outside : forall W a, Forall WOK W ->
    (usp + -128 <= a
     \/ (a < 0x60f000 /\ ~ (0x5ed1ec <= a < 0x5ed1f0) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5dc950 <= a < 0x5ec950))
     \/ (0x7fff7000 <= a < 0x10007fff8000)) -> outside W a.
Proof.
intros W a HW Ha. pose proof geo as (_ & G2 & _). eapply WOKb_outside; [| exact HW| exact Ha].
lia. Qed.

  Lemma WOKb_appW : forall hi W, hi <= usp + 24 -> Forall (WOKb hi) W -> appW W.
Proof.
pose proof geo as (G1 & G2 & G3 & _). unfold KHIGH in G3. atop_facts. intros hi W Hhi.
induction W as [|[lo1 hi1] W IH]; intros HW; [apply Forall_nil|]. inversion HW as [|x l H1 H2]; subst.
constructor; [| apply IH; exact H2]. unfold WOKb, ablk, ASTAGE, AIMG_HI, KLS, KHIGH in H1. cbn [fst snd] in H1 |- *. unfold KLOW, KHIGH. lia.
Qed.
  Lemma WOK_appW : forall W, Forall WOK W -> appW W.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_ctx ()) ["CANSEC1"; "CTX"] "h02Hah14__x1h21Hh32HWh41Wh57__arithh64__ffh77__sat17h87__sat18h97__sat19h:8__varmaph;5__witp;2p;1p;3p;4p;7g00]8j2VTg00C@j1=Tg01>Ij3JTg006mj10Tg01@_j1RTg00<Hj28Tg01X:j1ITg00dcj12Tg00:Lj14Tg01WDj1UTg00:0j27Tg00@Tj2TTg01Y8j2QTg00@8j2;Tg00_7j2MTg01Y`j3LTg01ZDj2KTg01?Gj2HTg00;hj1ETg00C`j2DTg00E:j1CTg00EXj1FTg00FCj2GTg00GQj2<Tg00H4j39Tg00Ffj4BTg00Qfj7ATg00I9j2@Tg00I[j2NTg00J5j2?Tg00Jaj3OTg00K;j3PTg00KZj4>Tg02bYj4STf0R0#0#0p=5%20#2#2#2p=1%00#0#0#0p=:%00#0#0#0#0#0#0#0p=6g00X]R1/70p=3g00U<R2/V2R3#=g02_4=J30p,3uspR3g00X8R4#0R5#0#5R6#0#5#RR7'8f1R8p,2rcR9#I%24R:#2#1#1#1R;#0#1#1#0#5#:#6#6#4%U9R9'7%2;#1#1#0#5#:#6#6#4,79'T%45R9%15#4R5'Q1;19%351M95R;,;1[[%39R<g01[XR=AL958UW0%3;\=^0<%46R6,K3%33%361H36#3[[g00Z>R6#E%=61D28%C2%F2R6g00V9g00VXR<P<g00W8R<P21G24R41<27592g00Zj%0:#5#4R:,<29924CBg00WXFA1@6<P0f2R<g00\8R6g00\XR4'N1?0<=O64dAP218C>b6b:b;X121807180:'7^12P0P3O1b5b7b8b9b2P0CSW3W4o"). Qed.

  
  Lemma ABASE_of_parts : forall hi W m m' so, ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono bsegs m m' ->
    ASTAT m -> rw_cells bsegs m ssp_guard [C8 canary] -> atrun_cells0 m -> harness_invA m -> rodata_sh0 m ->
    rclean m RSTK -> rclean m RBstdout -> rclean m RSTG -> stdout_file m so ->
    stk bsegs m' ALO (usp + -128) -> mem_inv bsegs m' -> AMFRAME m' -> stderr_wfile0 m' ->
    (exists errv, rw_cells bsegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    ABASE so m'.
Proof.
intros hi W m m' so Hhi HW MU WM AS GU TR HI ROD RCS RCB RSG SOF ST' MI' FR' SE' ERR'.
pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG. pose proof (WOKb_appW hi W ltac:(lia) HW) as AW.
pose proof (fun a => WOKb_outside hi W a ltac:(lia) HW) as OUT.
split; [exact ST'|]. split; [exact MI'|]. split; [exact FR'|].
split. { eapply ASTAT_agree; [exact AG| | exact AS]. intros a Ha. apply OUT. right.
unfold astat_addr, astat_app, astat_sh in Ha. rewrite ?shad_div in Ha. unfold ASHOFF in Ha. lia. }
split; [exact SE'|].
split. { eapply rw_cells_magree; [exact AG| exact GU| intros a Ha; apply OUT; unfold ssp_guard in Ha; cbn in Ha; lia]. }
split. { eapply atrun_cells0_magree; [exact AG| | exact TR]. intros a Ha. apply OUT. right; left.
unfold atrun0_addrA, atx_state_addrA, atx_addrA, AINIT_FLAG in Ha. lia. }
split. { exact I. }
split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
split; [eapply rclean_transport; [exact RSG| exact MU| exact WM| exact AW]|]. split; [exact ERR'|].
eapply stdout_file_magree; [exact AG| | exact SOF]. intros a Ha. apply OUT. cbn in Ha. lia.
Qed.

  Lemma ABASE_munch : forall W m m' so, ABASE so m -> Forall WOK W -> munch W m m' -> wmono bsegs m m' ->
    mem_inv bsegs m' -> stk bsegs m' ALO (usp + -128) -> stderr_wfile0 m' ->
    (exists errv, rw_cells bsegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    ABASE so m'.
Proof.
intros W m m' so (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF) HW MU WM MI' ST' SE' ERR'.
pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
eapply (ABASE_of_parts (usp + -128)); try eassumption; [lia|].
unfold AMFRAME in *. eapply rw_cells_magree; [eapply magree_of_munch; [exact MU| exact WM]| exact FR|].
intros a Ha. apply WOK_outside; [exact HW|]. cbn in Ha. lia.
Qed.

  Lemma astring_munch : forall hi W m m' P str slack r, ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono bsegs m m' ->
    astring m P str slack r -> astring m' P str slack r.
Proof.
intros hi W m m' P str slack r Hhi HW MU WM AS. pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
pose proof (astring_facts _ _ _ _ _ AS) as (F1 & _).
destruct AS as (BY & HF & SL & LEN & LO & RC & IR & RLO). pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
pose proof (bytes_at_bound _ _ _ _ BY) as B. rewrite length_app, zb_length in B. cbn [length] in B.
pose proof (rclean_shclean _ _ RC) as (_ & HUL & _). unfold hull64, KEND in HUL. unfold inreg in IR.
unfold astring. repeat match goal with |- _ /\ _ => split end; try assumption.
- eapply bytes_at_magree; [exact AG | exact BY |]. intros a Ha. rewrite length_app, zb_length in Ha. cbn [length] in Ha.
eapply WOKb_outside; [| exact HW|]; unfold zlength, KHIGH in *; lia.
- eapply rclean_magree; [exact AG | | exact RC]. intros a Ha. eapply WOKb_outside; [| exact HW|]; [lia|]. right; right.
rewrite !shad_div in Ha. unfold ASHOFF in Ha. unfold KHIGH, KEND in *. atop_facts. Z.div_mod_to_equations. lia.
Qed.

  
  

  
  Lemma exit_relro_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m ->
       rw_cells bsegs m 0xb2e00 [C8 (Z_to_bv 64 0xb1bc0); C8 (Z_to_bv 64 0xb1bb0)]
    /\ rw_cells bsegs m 0xb1bb0 [C8 (Z_to_bv 64 0x969cc); C8 (Z_to_bv 64 0x3072c)]
    /\ rw_cells bsegs m 0xb20f8 [C8 (Z_to_bv 64 0xa1b28); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m 0xb2dc0 [C8 (Z_to_bv 64 0xb69f0); C8 (Z_to_bv 64 0xb6c30)]
    /\ rw_cells bsegs m 0xb2148 [C8 (Z_to_bv 64 0xb3fa8)]
    /\ rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
Proof.
Ltac relro_tac AH bs :=
      eapply rw_cells_recast;
      [ apply (rw_cells_image0 bsegs _ _ bs);
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply (AI_relro AI _ _ _ _ _ AH); rewrite ?length_app, ?length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
        | vm_compute; reflexivity | lia | rewrite ?length_app, ?length_le8; lia ]
      | cbn; repeat split; exact I | reflexivity | reflexivity ].
intros L RNG st LB m AH. unfold got_ssp, ssp_guard.
Ltac cells_bs cells := lazymatch cells with
  | cons (C8 ?v) nil => constr:(le8 v)
  | cons (C8 ?v) ?t => let r := cells_bs t in constr:(le8 v ++ r)
  end.
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- rw_cells _ _ _ ?cells => let bs := cells_bs cells in relro_tac AH bs end.
Qed.

  Lemma mdtor_rt_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells bsegs m 0xb7b10 [C4 (Z_to_bv 64 1)] -> mdtor_rt m.
Proof.
intros L RNG st LB m AH RG. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. unfold artcells in RT. decompose [and] RT.
destruct (exit_relro_of_aheap _ _ _ _ _ AH) as (_ & _ & _ & _ & X5 & _).
unfold mdtor_rt. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.

  
  Lemma aat_exit_intro : forall (code : Z) (s : APS) L (LB : list ablock) (SP : Z) RNG
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk bsegs m ALO SP -> ALO <= SP - 48 - MDTOR_DEPTH -> usp + -128 <= SP <= usp ->
    ASTAT m -> AHEAP AI L RNG (aps_m s) LB m -> stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] ->
    mem_inv bsegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    aat_exit code s RNG (MS (mkR ra (Z_to_bv 64 SP) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 AEXIT_PC) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LOS SPR AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
pose proof AS as (A1 & A2 & (cdt & thr & sec & tm1 & A3) & [reg AX] & A12 & [dso A13] & A14 & A15 & A15' & A16 & A17
& D1 & D2 & D3 & GD & SH1 & SH2).
destruct (exit_relro_of_aheap _ _ _ _ _ AH) as (X1 & X2 & X3 & X4 & X5 & X6).
pose proof (mdtor_rt_of_aheap _ _ _ _ _ AH D1) as RT.
unfold aat_exit. do 33 eexists. exists m, ALO, TID, cdt, thr, sec, tm1, dso, canary.
split; [reflexivity|].
rewrite !unsigned_lit by lia.
split. { unfold mdtor_pre. repeat match goal with |- _ /\ _ => split end; try assumption; eexists; eassumption. }
repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try lia.
all: try (exists reg; exact AX).
- eapply rng_sub'; [exact RSTK'| lia].
- unfold MDTOR_W. repeat (apply Forall_cons; [cbn [fst snd]|]); [..| apply Forall_nil].
all: first [ eapply rng_sub'; [exact RIMG| lia] | eapply rng_sub'; [exact RIMSH| lia] ].
Qed.

  
  Lemma amain_return : forall (code : Z) (s : APS) L (LB : list ablock) RNG
      (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
    AMFRAME m -> stk bsegs m ALO (usp + -128) -> ASTAT m -> AHEAP AI L RNG (aps_m s) LB m ->
    stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] -> mem_inv bsegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    evtF bsegs RNG (aat_exit code s RNG)
      (MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x7fce8) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR ST AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
unfold AMFRAME, ASTAGE2_RET in FR.
do 11 zstep. release_frame FR ST (usp + -48). zstep.
let v := eval cbv in ASTAGE2_RET in replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; rpc).
zstep.
apply evtF_done. unfold AEXIT_PC.
eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia].
Qed.

  
  Lemma aexit2_tail : forall (s : APS) L (LB : list ablock) RNG
      (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk bsegs m ALO (usp + -128) -> ASTAT m -> AHEAP AI L RNG (aps_m s) LB m ->
    stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] -> mem_inv bsegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    evtF bsegs RNG (aat_exit 2 s RNG)
      (MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x7fd74) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
zstep. zstep.
apply evtF_done. unfold AEXIT_PC.
eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia].
Qed.
End CTX.
End CANSEC1.
