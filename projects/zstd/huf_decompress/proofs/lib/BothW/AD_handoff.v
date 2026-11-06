(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem Mem Cells Frame.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps BothHandoff.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow ModelX.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsBoth BothEntry.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel BothMain.     (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_iface MonadF Strnlen_iface AExit F_module_dtor ADriver_iface AD_kit AD_ctx AD_main_A AD_main_B4 AD_main_C AD_main AD_main_pack AMain_asm AFake_iface ALayout ARepInit_kit AD_handoff0.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import AHarness_bm.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AD_handoff () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01C59OSSVerify5KrLib5BothW<ARepInit_kit2LVC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase7alayout01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_UC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AD_handoff4LDRVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface2HUC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5BothW5ABase:AMALLOC_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8AFREE_PCC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib5BothW>AHarness_iface<AFMALLOC_RETC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5BothW>AHarness_iface<AFREE_DT_RETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface<AFREE_WK_RETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface<AFREE_DB_RETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface:AFREEP_RETC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib2AS:MainExport8allow_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport8aallowedC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib2AS=MainFactsBoth8asan_visC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherC49OSSVerify5KrLib8BothMain:amain_openC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC59OSSVerify5KrLib4Spec;BothHandoff7atop_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AMain_asm4RNG0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;BothHandoff7resv_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AD_main:apat_mainAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface8aresv_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run?valid_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC49OSSVerify5KrLib8TopLevelBvalid_entry_eitherC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs8valid_fsC4ELinuxProcessSemantics?LinuxProcessSem5State;in_image_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs@fs_keys_relativeC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_credsC4ELinuxProcessSemantics?LinuxProcessSem5State9in_nofileC4ELinuxProcessSemantics?LinuxProcessSem3Run<valid_nofileC4ELinuxProcessSemantics?LinuxProcessSem3Run=valid_sigmaskC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_hwcapC4ELinuxProcessSemantics?LinuxProcessSem5State:in_va_sizeC4ELinuxProcessSemantics?LinuxProcessSem3Run=valid_urandomC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyK47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib2AS9BothEntry4WblkC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC59OSSVerify5KrLib2AS9BothEntry:hidden_argC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem3Run7en_drawC59OSSVerify5KrLib2AS:MainExport8pfact_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9BothEntry8ashadow0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib2AS9BothEntry@asan_mem_facts_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9BothEntryAasan_pure_facts_wC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib5BothW:AD_handoff4A0I'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff09tid_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC47Corelib4Init5Logic5proj1C4ELinuxProcessSemantics?LinuxProcessSem3RunFtotal_arg_bytes_nonnegC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5BothW6AD_ctx3ALOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_sp0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<ARepInit_kit6LV_sp0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7div_modK46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMemHlength_entry_stack_imageC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC59OSSVerify5KrLib3Lib7InitMemHbuild_stack_bytes_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem7raw_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem7pad_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem>raw_len_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem;struct_sizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib3Lib7InitMem8str_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0;SBLK_lengthC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_spanK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5BothW;AD_handoff08arg_packC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5r_rloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5r_rhiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5inregC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib5BothW9Stdio_kit7shcleanC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List9nth_errorC47Corelib5Lists7ListDef3nthC46Stdlib5Lists4List=nth_error_nthC59OSSVerify5KrLib3Lib7InitMem8str_ptrsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_NoneC59OSSVerify5KrLib5BothW9AD_main_A6AENTRYC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AD_handoff5RSTK0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indc59OSSVerify5KrLib5BothW:AD_handoff7HU_LDRVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;Stdio_iface=stderr_wfile0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ADriver_iface<atrun_cells0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface<harness_invAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ADriver_iface:rodata_sh0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AD_main_A5AARGVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AD_main_A4RNGSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ADriver_iface4ASTGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AProg_kit6aps_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps5aps_mC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0;astat_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AF_atexit:atx_stateAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0;gdescs_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=F_module_dtor6gdescsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff09astat_shGC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff09astat_shDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AD_ctx5ASTATC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW9Stdio_kit6region01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0Bstderr_wfile0_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0>ssp_guard_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0Batrun_cells0_init'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0@atx_stateA0_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0@rodata_sh0_init'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0Bstack_shclean_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0Frclean_stdout_buf_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0Arclean_stage_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0:errno_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0@stdout_file_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps8aps_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps8aps_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0>argv_ptrs_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AD_ctx7astringC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib6Common8DrvAgreeDzbytes_map_unsigned'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AD_main_A9arg_factsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib5BothW;AD_handoff0=rng_stacksideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0@rng_stackside_shC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff09rng_imageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0<rng_image_shC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF4rng0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF5fp_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff09rng_emptyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit6hull64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow7app_blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4rrngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0@stage2_word_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff09astg_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;BothHandoff<a_space_beg0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;BothHandoff<a_ptr_array0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps8aps_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface5AHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport8mfact_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8BothMain7amodelHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib4LibA6ModelX2MXC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula07C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C59OSSVerify5KrLib5BothW;AD_handoff04SBLKC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:StdioFiles;stdout_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps6aps_soC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize00K4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes3nat01I59OSSVerify5KrLib2AS:MainExport5mfact00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=MainFactsBoth>asan_mem_factsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS:MainExport5pfact00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=MainFactsBoth?asan_pure_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg7b_phdrsC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI59OSSVerify5KrLib5BothW9Stdio_kit6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit8RBstdoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ADriver_iface4RSTGC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AExit;stdin_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport5two64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib5BothW4BImg9b_init_pcC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC59OSSVerify5KrLib2AS9BothEntry3ARAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9BothEntry3AGPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9BothEntry3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9BothEntry5AMAINC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathK47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9auxv_sizeI47Corelib4Init5Logic4True00C59OSSVerify5KrLib2AS9BothEntry5KHIGHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AD_handoff4UDRVC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeK47Corelib4Init5Logic4True01C46Stdlib5Lists4List6nth_okC59OSSVerify5KrLib5BothW=ADriver_iface;ASTAGE2_RETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ADriver_iface8AMAIN_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=F_module_dtor8AGLOBALSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AExit6RSTDINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4KENDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AD_ctx>errno_addr_ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ADriver_iface4RFMTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ADriver_iface@ashenv_law_holdsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<AD_main_pack=adrv_of_walksC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AD_handoffAapat_main_extractC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AMain_asm<A0_init_stmtC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport5pfact01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff0<ho_pfact_eqbC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport5pfact03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff08rng_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AD_handoff08rng_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_VC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_iface9afake_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AD_handoff@rng_fs_init_stmtC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC59OSSVerify5KrLib5BothW;AD_handoff0=ho_pfact_findC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4LibA6ITreeA3alwC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition UDRV : list (list Z) :=
  [[AMALLOC_PC; 0x7fb40]; [AMALLOC_PC; 0x7fb94]; [AFREE_PC; 0x7fbb8]; [AFREE_PC; 0x7fce8];
   [AMALLOC_PC; 0x7fe20]; [AFREE_PC; 0x7feb4]; [AMALLOC_PC]; [AFREE_PC];
   (* [comment removed for export] *)
   [AMALLOC_PC; AFMALLOC_RET]; [AFREE_PC; AFREE_DT_RET]; [AFREE_PC; AFREE_WK_RET]; [AFREE_PC; AFREE_DB_RET];
   [AFREE_PC; AFREEP_RET]]%Z.

(* [comment removed for export] *)
Definition LDRV (V : nat -> Z) (w : bool) : alayout := mkALayout (LV V) w UDRV.   (* [comment removed for export] *)

Lemma HU_LDRV : forall V w, HU (LDRV V w).
Proof. intros V w. unfold HU, LDRV, UDRV. cbn [al_U]. repeat split; cbn; tauto. Qed.

(* [comment removed for export] *)
Definition RSTK0 (usp : Z) : region := mkRegion (ALO usp) (usp + -112) (ALO usp - usp mod 64) (usp - usp mod 64).

Section Handoff.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.
  Variable A0 : (nat -> Z) -> alw.
  Hypothesis A0I : A0_init_stmt A0.

  (* [comment removed for export] *)
  Definition aheap_init_stmt : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp -> amain_open en inp w V m ms mo ->
      atop_of (en_sp en) = ATOP ->
      AHEAP AI (LDRV V w) (RNG0 A0 V mo) (aps_m (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP)) [] m.
  Hypothesis AHEAP_INIT : aheap_init_stmt.

  (* [comment removed for export] *)
  Definition aresv_init_stmt : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp -> amain_open en inp w V m ms mo ->
      aresv_ok (LDRV V w) (resv_of V).
  Hypothesis ARESV_INIT : aresv_init_stmt.

  (* [comment removed for export] *)
  Definition rng_fs_init_stmt : Prop :=          (* [comment removed for export] *)
    forall V w mo, Forall (pfact_ok V) asan_pure_facts -> 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->
      rng_fs (LDRV V w) (RNG0 A0 V mo).
  Hypothesis RNGFS_INIT : rng_fs_init_stmt.

  Lemma A0I' : forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> A0 V p.
Proof. intros V p H1 H2. apply A0I; assumption. Qed.

  Theorem apat_main_extract : forall en inp w V m ms mo,
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp -> amain_open en inp w V m ms mo ->
    atop_of (en_sp en) = ATOP ->
    exists L, apat_mainA AI rng_fs L (RNG0 A0 V mo) inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ms.
Proof.
    intros en inp w V m ms mo VE VI AM HA. exists (LDRV V w).
    pose proof (AHEAP_INIT en inp w V m ms mo VE VI AM HA) as AH. pose proof (ARESV_INIT en inp w V m ms mo VE VI AM) as ARK.
    destruct en as [sp brk0 mbase rdraw]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ VI) in VE. destruct VE as (VSP & _ & _ & FITS). cbn [en_sp en_draw] in *.
    destruct VSP as (SPLO & SPHI & SP16). unfold sp_window_lo in SPLO. unfold sp_window_hi in SPHI. unfold entry_stack_fits, sp_window_hi in FITS.
    pose proof VI as (VARGV & VENVP & _).
    destruct AM as (Hms & HVR & PIN & HMF & HPF & MI & ST & HID & SH0 & AMOD). cbn [en_sp en_brk en_draw] in *.
    apply Forall_app in HMF as [HM HMW]. apply Forall_app in HPF as [HP HPW].
    destruct PIN as (PV0 & PV6 & PV10 & USP & PV1 & PV2 & PV3 & PV7 & PV4 & PV5 & PV8 & PV9).
    unfold atop_of in HA.
    set (usp := bv_unsigned sp) in *.
    set (argv := in_argv inp) in *. set (envp := in_envp inp) in *.
    set (RNG := RNG0 A0 V mo).
    assert (HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP) by (rewrite USP; exact HA).
    assert (USP3 : 32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) = usp) by (clear - USP; lia).
    pose proof (A0I' V) as AL. change (A0 V) with (A0 V) in AL.
    assert (RNGE : RNG = fp_ok (m_vm_lazy (MX mo [])) (A0 V)) by reflexivity.
    pose proof (tid_range V HP) as TID.
    pose proof (argc_pos := proj1 VARGV). cbv beta in argc_pos.
    assert (SPAN24 : usp + 24 <= 2^47).
    { unfold entry_stack_span in FITS. pose proof (Run.total_arg_bytes_nonneg argv). pose proof (Run.total_arg_bytes_nonneg envp). subst argv envp. lia. }
    assert (USPLO : ATOP + 8388608 <= usp) by (subst usp; lia).
    assert (GEO : ATOP <= ALO usp /\ ALO usp + 8388608 - 4096 = usp /\ KHIGH <= ALO usp) by (unfold ALO, KHIGH in *; lia).
    destruct GEO as (G1 & G2 & G3).
    assert (SPG : usp = al_sp0 (LDRV V w)) by (unfold LDRV; rewrite LV_sp0; lia).
    assert (TOPR : usp - 160 <= al_top (LDRV V w) <= 2^47).
    { unfold al_top. rewrite <- SPG. unfold page_round_up_Z, page_size. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
    assert (TOPR' : al_top (LDRV V w) <= usp + 3935) by (unfold al_top; rewrite <- SPG; unfold page_round_up_Z, page_size; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
    assert (BOT : ATOP + 4096 <= ALO usp) by (unfold ALO; lia).
    assert (M64 : 0 <= usp mod 64 < 64 /\ (usp - usp mod 64) mod 64 = 0 /\ (ALO usp - usp mod 64) mod 64 = 0).
    { unfold ALO. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
    destruct M64 as (M64a & M64b & M64c).
    assert (IMGHI : usp + Z.of_nat (length (entry_stack_image b_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw)) <= 2^64).
    {
      pose proof (length_entry_stack_image b_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw) as ILS.
      pose proof (build_stack_bytes_length b_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw) as BL.
      pose proof (raw_len_nonneg argv envp) as (R1 & R2 & R3 & R4).
      unfold entry_stack_span in FITS. unfold raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc in BL.
      change (Z.of_nat auxv_size) with 160 in FITS. clear - ILS BL R2 R3 R4 FITS SPHI. lia. }
    assert (SPLO' : stack_max_size <= usp) by (unfold stack_max_size; lia).
    assert (HID' : forall z, str_base sp argv envp <= z < str_base sp argv envp + Z.of_nat (length (SBLK argv envp)) ->
                     m (wa z) = wrap_mem b_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw (wa z)).
    { intros z Hz. apply HID. unfold hidden_arg. cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap]. right.
      rewrite SBLK_length in Hz. unfold str_base, struct_size, Lib.InitMem.argc, Lib.InitMem.envc in Hz.
      unfold Wblk. cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap]. rewrite build_stack_bytes_length.
      pose proof (raw_len_nonneg argv envp) as (_ & R2 & R3 & R4).
      unfold raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc. unfold pad_len, raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc in Hz, R4 |- *.
      subst argv envp usp. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
    assert (A0S : exists s0, nth_error argv 0 = Some s0 /\ nth 0 argv [] = s0).
    { subst argv. destruct (in_argv inp) as [|a l]; [cbn in argc_pos; lia|]. exists a. split; reflexivity. }
    destruct A0S as (s0 & Hn0 & En0).
    destruct (arg_pack V sp argv envp (in_uid inp) (in_hwcap inp) rdraw m HM HP SPLO' IMGHI SP16 USPLO HAT FITS VARGV HID' 0 s0 Hn0)
      as (off0 & slack0 & RA0 & Hp0 & Ho0 & BY0 & SL0 & P024 & SC0 & LT0 & IR0 & RLO0 & RLO0' & RHI0 & END0).
    assert (Eoff0 : off0 = 0).
    { subst argv. destruct (in_argv inp) as [|a l]; [discriminate|]. cbn in Hp0. injection Hp0. lia. }
    assert (A1S : exists P1 (slack1 : list byte) (RA1 : region),
              2 <= Z.of_nat (length argv) ->
              P1 = str_base sp argv envp + Z.of_nat (length s0) + 1
              /\ bytes_at bsegs m P1 (nth 1 argv [] ++ Z_to_bv 8 0 :: slack1)
              /\ (- (P1 + Z.of_nat (length (nth 1 argv [])) + 1)) mod 8 <= zlength slack1
              /\ usp + 24 <= P1
              /\ shclean m (r_lo RA1) (r_hi RA1) (r_rlo RA1) (r_rhi RA1) /\ r_lo RA1 < r_hi RA1
              /\ inreg RA1 P1 (Z.of_nat (length (nth 1 argv [])) + 1 + zlength slack1)
              /\ usp + -112 <= r_rlo RA1 /\ ATOP <= r_rlo RA1 /\ r_rhi RA1 <= 2^47
              /\ P1 + Z.of_nat (length (nth 1 argv [])) + 1 + zlength slack1 <= 2^47).
    { destruct (nth_error argv 1) as [s1|] eqn:Hn1.
      - destruct (arg_pack V sp argv envp (in_uid inp) (in_hwcap inp) rdraw m HM HP SPLO' IMGHI SP16 USPLO HAT FITS VARGV HID' 1 s1 Hn1)
          as (off1 & slack1 & RA1 & Hp1 & Ho1 & BY1 & SL1 & P124 & SC1 & LT1 & IR1 & RLO1 & RLO1' & RHI1 & END1).
        assert (En1 : nth 1 argv [] = s1) by (apply nth_error_nth; exact Hn1).
        assert (Eoff1 : off1 = Z.of_nat (length s0) + 1).
        { clear - Hp1 Hn0 Hn1. destruct argv as [|a [|b l]]; try discriminate. cbn in Hn0, Hp1. injection Hn0 as ->. injection Hp1. lia. }
        exists (str_base sp argv envp + off1), slack1, RA1. intros _. rewrite En1. subst off1.
        repeat match goal with |- _ /\ _ => split end; try assumption. all: lia.
      - exists 0, [], RA0. intros H2. exfalso. apply nth_error_None in Hn1. lia. }
    destruct A1S as (P1 & slack1 & RA1 & A1F).
    unfold apat_mainA.
    exists usp, (V 44%nat), (Z_to_bv 64 (usp + 8)), (Z_to_bv 64 (Z.of_nat (length argv))), (Z_to_bv 64 AMAIN), (Z_to_bv 64 (usp + 8 * Z.of_nat (length argv) + 16)),
           (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0).
    exists (RSTK0 usp), (Z_to_bv 64 (V 45%nat)), (str_base sp argv envp), P1, slack0, slack1, RA0, RA1.
    unfold RSTK0. cbn [r_lo r_hi r_rlo r_rhi].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SP16|]. split; [exact USPLO|]. split; [exact SPAN24|].
    split; [lia|]. split; [exact SPG|]. split; [exact BOT|].
    do 8 (split; [unfold LDRV, UDRV; cbn; tauto|]). split; [apply HU_LDRV|].
    split; [subst argv; exact VARGV|].
    unfold AENTRY. subst ms.
    exists (Z_to_bv 64 (V 664%nat)), (Z_to_bv 64 (V 665%nat)), (Z_to_bv 64 (V 666%nat)),
           (Z_to_bv 64 (usp + 8 * Z.of_nat (length argv) + 16)), (Z_to_bv 64 0x6000000000000000),
           (Z_to_bv 64 (V 667%nat)), (Z_to_bv 64 (V 668%nat)), (Z_to_bv 64 (V 669%nat)), (Z_to_bv 64 (V 670%nat)),
           (Z_to_bv 64 (V 671%nat)), (Z_to_bv 64 (V 672%nat)), (Z_to_bv 64 (V 673%nat)), (Z_to_bv 64 (V 674%nat)), m.
    split. { unfold ASTAGE2_RET, AMAIN_PC, AMAIN, ATP, BothEntry.ARA, BothEntry.AGP, BothEntry.ATP, BothEntry.AMAIN. subst argv. replace (usp + -48) with (usp - 48) by lia. reflexivity. }
    split. { destruct (stk_split _ _ (usp - 8388608) (ALO usp) usp ST ltac:(unfold ALO; lia)) as [_ ST2]. exact ST2. }
    split; [exact MI|].
    pose proof (astat_cells V m HM) as AC. pose proof (gdescs_init V m HM) as GD.
    pose proof (astat_shG V m HM) as SHG. pose proof (astat_shD V m HM) as SHD.
    decompose [and] AC.
    split. { unfold ASTAT. repeat match goal with |- _ /\ _ => split end; try assumption. }
    split; [exact (stderr_wfile0_init V m HM)|].
    split; [exact (ssp_guard_init V m HM)|].
    split; [exact (conj (atrun_cells0_init' V m HM) (atx_stateA0_init V m HM))|].
    split. { exact I. }
    split; [exact (rodata_sh0_init' V m HM)|].
    split. { unfold rclean. cbn [r_lo r_hi r_rlo r_rhi]. split; [| lia]. apply (stack_shclean_init V m HM HP HAT); unfold ALO, Shadow.KEND in *; lia. }
    split; [exact (rclean_stdout_buf_init V m HM)|].
    split; [exact (rclean_stage_init V m HM)|].
    split. { exists (Z_to_bv 64 0). rewrite errno_addr_ATP. exact (errno_init V m HM). }
    split; [exact (stdout_file_init V m HM)|].
    split; [reflexivity|].
    split. { split; [exact ARK| reflexivity]. }
    split; [exact AH|].
    pose proof (argv_ptrs_init V m HM) as [AP0 AP1].
    split. { unfold AARGV. split; [| split].
      - rewrite USP3 in AP0. cbn [u64s]. rewrite app_nil_r.
        replace (str_base sp argv envp) with (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (16 * V 6%nat + 4096 * V 10%nat))) + 184); [exact AP0|].
        unfold str_base, struct_size, Lib.InitMem.argc, Lib.InitMem.envc. subst argv envp. rewrite PV1, PV2. fold usp. lia.
      - unfold astring. fold argv. rewrite En0. rewrite Eoff0, Z.add_0_r in *.
        repeat match goal with |- _ /\ _ => split end; try assumption.
        + unfold F_fmt_fp_lib.zb. rewrite (zbytes_map_unsigned' s0). exact BY0.
        + destruct (arg_facts 0 argv VARGV 0) as [F _]. rewrite En0 in F. exact F.
        + unfold zlength in *. rewrite length_map. exact SL0.
        + destruct (arg_facts 0 argv VARGV 0) as [_ F]. rewrite En0 in F. exact F.
        + unfold rclean. split; [exact SC0| exact LT0].
        + unfold zlength in *. rewrite length_map. exact IR0.
        + clear - RLO0. lia.
      - intros HARGC2. fold argv. destruct (A1F HARGC2) as (EP1 & BY1 & SL1 & P124 & SC1 & LT1 & IR1 & RLO1 & RLO1' & RHI1 & END1). split.
        + rewrite USP3 in AP1. cbn [u64s]. rewrite app_nil_r.
          replace P1 with (Z.b2z ((1 mod two64) <? (V 1%nat mod two64)) * (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (V 3%nat + (16 * V 6%nat + 4096 * V 10%nat)))) + 185)); [exact AP1|].
          rewrite EP1. unfold str_base, struct_size, Lib.InitMem.argc, Lib.InitMem.envc. rewrite <- En0 in *. rewrite PV3. subst argv envp. rewrite PV1, PV2. fold usp.
          unfold two64. rewrite (Z.mod_small 1) by lia. rewrite Z.mod_small by lia.
          replace (1 <? Z.of_nat (length (in_argv inp))) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. lia.
        + unfold astring.
          repeat match goal with |- _ /\ _ => split end; try assumption.
          * unfold F_fmt_fp_lib.zb. rewrite (zbytes_map_unsigned' (nth 1 argv [])). exact BY1.
          * destruct (arg_facts 0 argv VARGV 1) as [F _]. exact F.
          * unfold zlength in *. rewrite length_map. exact SL1.
          * destruct (arg_facts 0 argv VARGV 1) as [_ F]. exact F.
          * unfold rclean. split; [exact SC1| exact LT1].
          * unfold zlength in *. rewrite length_map. exact IR1.
          * clear - RLO1. lia. }
    split. { unfold RNGS. subst RNG. unfold RNG0, rrng, RFMT, RBstdout. cbn [r_rlo r_rhi].
      pose proof (rng_stackside (m_vm_lazy (MX mo [])) (A0 V) V AL HP HAT) as RS. pose proof (rng_stackside_sh (m_vm_lazy (MX mo [])) (A0 V) V AL HP HAT) as RSS.
      pose proof (rng_image (m_vm_lazy (MX mo [])) (A0 V) V AL) as RI. pose proof (rng_image_sh (m_vm_lazy (MX mo [])) (A0 V) V AL) as RIS.
      unfold BothEntry.ACEIL in *. fold argv. rewrite En0. rewrite Eoff0, Z.add_0_r in *.
      repeat match goal with |- _ /\ _ => split end.
      - apply RS; lia.
      - apply RS; lia.
      - apply RI; lia.
      - apply RIS; lia.
      - apply RNGFS_INIT; [exact HP| exact HAT].
      - apply RSS; rewrite !shad_div; unfold AsanEmbed.ASHOFF; clear - SPLO SPHI HA G2 BOT M64a; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
      - replace (shad 0x10000) with 2147459072 by reflexivity. replace (shad 0x20dc0) with 2147467704 by reflexivity. apply RIS; lia.
      - replace (shad 0x60d980) with 2148244272 by reflexivity. replace (shad 0x60ddc0) with 2148244408 by reflexivity. apply RIS; lia.
      - intros b Hb. apply rng_empty. exact Hb.
      - apply RS; unfold zlength in *; rewrite ?length_map; lia.
      - destruct SC0 as (_ & HL0 & _). unfold hull64, Shadow.KEND in HL0.
        apply RSS; rewrite !shad_div; unfold AsanEmbed.ASHOFF; clear - RLO0' RHI0; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
      - intros HARGC2. destruct (A1F HARGC2) as (EP1 & BY1 & SL1 & P124 & SC1 & LT1 & IR1 & RLO1 & RLO1' & RHI1 & END1).
        unfold BothEntry.ACEIL in RLO1'. split.
        + apply RS; unfold zlength in *; rewrite ?length_map; lia.
        + destruct SC1 as (_ & HL1 & _). unfold hull64, Shadow.KEND in HL1.
          apply RSS; rewrite !shad_div; unfold AsanEmbed.ASHOFF; clear - RLO1' RHI1; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
    split. { pose proof (stage2_word_init V m HM) as S2W. rewrite USP3 in S2W. exact S2W. }
    exact (astg_init V m HM).
  Qed.

  (* [comment removed for export] *)
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv (aci AI).
  Hypothesis CI_WF : forall iv, In iv (aci AI) -> 0 <= fst iv.
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis FUZZ : fuzz_oneA_stmtB AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.

  Theorem adrv_closed : adrv_stmt A0.
Proof.
    eapply adrv_of_walks; first [ exact apat_main_extract | exact (ashenv_law_holds AI) | eassumption ].
  Qed.
End Handoff.

(* [comment removed for export] *)
Lemma afake_rng_init : forall A0, A0_init_stmt A0 -> rng_fs_init_stmt afake_rng A0.
Proof.
  intros A0 A0I V w mo HP HAT. unfold afake_rng, LDRV, al_fake, al_dtls, FAKESZ, RNG0. cbn [al_V LV Nat.eqb].
  pf V HP (PVar 377 1551 34359733495) P393. pf V HP (PVar 310 1 34359736319) P310.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW310.
  assert (B393 : 4096 <= 4096 * V 377%nat /\ 4096 * V 377%nat + 11571200 <= ATOP) by (clear - P393 P0 P6 P10 DW393 HAT; lia).
  assert (B310 : 4096 <= 4096 * V 310%nat /\ 4096 * V 310%nat + 4096 <= ATOP) by (clear - P310 P0 P6 P10 DW310 HAT; lia).
  pose proof (fun p => A0I V p) as AL.
  destruct (rng_fake (m_vm_lazy (MX mo [])) (A0 V) V AL B393) as [R1 R2].
  split; [exact R1|]. split; [exact R2|]. exact (rng_dtls (m_vm_lazy (MX mo [])) (A0 V) V AL B310).
Qed.
End CANSEC1.
