(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (9 recorded proofs replaced by written proofs (ASTAGE_LEN_Z, dmalloc_M, dfree_M and 6 more); the recorded proofs name the unit's interp_eff_accesses and stepF shims, proved equal to the model's). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree Stdio Driver Adapter AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto AMalloc_iface AProg_kit AHarness_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import F_syscalls StdioFiles Stdio_kit MonadF AF_atexit AExit F_module_dtor.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw DrvAgree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import AHarness_bm.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ADriver_iface () := "C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Z2Nat2idK47Corelib4Init6Specif3sig01K47Corelib7Numbers7BinNums8positive02I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C47Corelib4Init6Specif9proj2_sigc59OSSVerify5KrLib5BothW=ADriver_iface>astage_len_sigC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00K59OSSVerify5KrLib4Spec5ProgA6AAlloc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver>read_loop_bodyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AProg_kit6implMAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA@implF_epost_monoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5BothW=ADriver_iface:rodata_sh0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4LibA6Shadow<shadow_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5BothW;AHarness_bm7hinv_bmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit6hull64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow7app_blkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3minC59OSSVerify5KrLib4LibA6Shadow7gran_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib4LibA6Shadow8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4svalC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib5BothW9AProg_kit9wr_at_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic2or00K59OSSVerify5KrLib5BothW9Stdio_kit6region01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5r_rloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit5r_rhiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib5BothW=ADriver_iface4RFMTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4LibA6Shadow5KHIGHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4KENDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto9shad_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow@shadow_bytes_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4appWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kitDappW_shadow_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ShadowBshadow_bytes_munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame?wr_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AHarness_bm=hinv_bm_munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec<AsanProgDeps3APS00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps7aset_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps6aps_soC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K59OSSVerify5KrLib4Spec<AsanProgDeps3APS01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface8aat_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=F_module_dtor9mdtor_preC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AF_atexit:atx_stateAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:StdioFiles;stderr_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec5ProgA3AStC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA3ioAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:exit_modelC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF4rng0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver4io_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF5postFC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:StdioFiles;stdout_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=F_module_dtorAaexit_spec_closedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AExit6RSTDINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AExit;stdin_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_syscalls7got_sspC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AExit;MDTOR_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AExit7MDTOR_WC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes9Empty_set00c59OSSVerify5KrLib5BothW=ADriver_iface<aps_get_set'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface<aps_set_set'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface<aps_set_get'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface8AEXIT_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps:AAllocAsanC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC59OSSVerify5KrLib3Lib6MStateKinterp_eff_accesses_nv_shimC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5StepF<lift_resultFC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib4LibA5StepF9stepF_gnvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF=evtF_step_accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AProg_kit:implMA_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA;alloc_initAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00c59OSSVerify5KrLib5BothW=ADriver_ifaceBATARGET_ALLOC_INITC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA<alloc_countAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_ifaceCATARGET_ALLOC_COUNTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface5AHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:AI_rtcellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8artcellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit6ashenvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indI59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface:ashenv_lawC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps5aps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_UC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AProg_kit6aps_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps8aps_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface8aresv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps8aps_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps9amalloc_MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AProg_kit8aps_restC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface<dmalloc_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7amallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps6aset_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AProg_kit>implMA_amallocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface<dmalloc_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase=AMALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase:AMALLOC_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase;AMALLOC_SYMC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps7afree_MC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface:dfree_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5afreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AProg_kit<implMA_afreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface:dfree_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase;AFREE_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8AFREE_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AFREE_SYMC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesI59OSSVerify5KrLib5BothW5ABase6uchain00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C47Corelib4Init5Peano2ltC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revK59OSSVerify5KrLib5BothW5ABase6uchain01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5BothW=AMalloc_iface4aunwC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib5BothW5ABase6UDEPTHC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib5BothW=AMalloc_iface3aciC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:aheap_presC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib5BothW5ABase9in_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7in_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst9ATOP_al16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>AHarness_iface@astk_shadow_presC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewI47Corelib4Init5Logic4True00C59OSSVerify5KrLib5BothW=AMalloc_iface<amalloc_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface8aunw_drvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface9AI_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_ifaceNastk_shadow_pres_of_aheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9aptr_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:afree_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface7AI_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface?afree_null_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface?dfree_null_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface<AI_free_nullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface?dfree_null_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree6magreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface<atrun0_addrAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface<atrun_cells0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AF_atexit?atx_state_addrAC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib6Common8DrvAgree?rw_cells_magreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AF_atexit@atx_stateA_agreeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2c59OSSVerify5KrLib5BothW=ADriver_iface:AINIT_FLAGC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib5BothW=AMalloc_iface<aclient_addrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface7rin_ivsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface9adrv_presC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ADriver_iface9atrun_ivsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_trans".   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AMAIN_PC : Z := 0x7faec.           (* [comment removed for export] *)
Definition ASTAGE2_RET : Z := 0xa1544.       (* [comment removed for export] *)
Definition AEXIT_PC : Z := 0xa1c44.          (* [comment removed for export] *)
Definition ATARGET_ALLOC_INIT : Z := 0x7fdb0.
Definition ATARGET_ALLOC_COUNT : Z := 0x7fdb4.
Definition ATARGET_RUN : Z := 0x7fdbc.
Definition AEMIT_PRINTF : Z := 0x7ff44.
Definition AFUZZ_INIT : Z := 0.               (* [comment removed for export] *)
Definition AGOT_FUZZ_INIT : Z := 0xb2d90.    (* [comment removed for export] *)
Definition AINIT_FLAG : Z := 0x5ec950.        (* [comment removed for export] *)
Definition AAEF_ARGC : Z := 0xb66b8.         (* [comment removed for export] *)
Definition AGOT_STDERRP : Z := 0xb2d88.      (* [comment removed for export] *)
Definition ASTDERRP : Z := 0xb2020.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ASTAGE : Z := 0x5dc950.
Definition astage_len_sig : { n : nat | Z.of_nat n = 65536 }.
Proof.
ltac2:(KReplay.run1 (kr_t_ADriver_iface ()) ["CANSEC1"] "h01nh11mh21Hp;1p;3p;2p;4p-1R0p10000R1p4p710p8P0P1p4p7210p8g000Mj1;Tg000mj19Tg001Kj32Tg001ej1:Tg002Ej24Tg002bj21Tg003>j28Tg003^j27Tg0048j26Tg004Vj45Tg0052j13Tf0R1#3#3p=0g005WR0g0066R2%;1g006T#0#0#0#0#0#0#0#0#9R332X00%:3g0079g007TR0f1R4/41g0084R532f2R6/14[R711411464=205R8[f3/16\81841P4n2001000000120000000X12X02P7^12^02P1g008TP31705O3b2,63C5o"). Qed.
Definition ASTAGE_LEN : nat := proj1_sig astage_len_sig.
Lemma ASTAGE_LEN_Z : Z.of_nat ASTAGE_LEN = 65536.
Proof. exact (proj2_sig astage_len_sig). Qed.
Definition RSTG : region := mkRegion 0x5dc950 0x5ec950 0x5dc940 0x5ec980.
(* [comment removed for export] *)
Definition ASTG (m : amem) : Prop := exists sj, rw_cells bsegs m ASTAGE [CB ASTAGE_LEN sj].

(* [comment removed for export] *)
Definition ATARGET_RUN_STACK : Z := 80 + AHARNESS_STACK.

(* [comment removed for export] *)
Definition RFMT : region := mkRegion 0x10000 0x20dc0 0x10000 0x20dc0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition rodata_sh0 (m : amem) : Prop :=
  shadow_bytes m (shad 0x10000) (shad 0x20dc0) (fun _ => 0) /\ wr_at bsegs m (shad 0x10000) (shad 0x20dc0 - shad 0x10000)
  /\ hinv_bm m.   (* [comment removed for export] *)

Lemma rodata_sh0_rclean : forall m, rodata_sh0 m -> rclean m RFMT.
Proof.
  intros m [SB [WR _]]. unfold rclean, RFMT, shclean; cbn [r_lo r_hi r_rlo r_rhi]. split; [|lia].
  split; [| split; [unfold hull64, KEND; lia| split; [eapply wr_at_sub; [exact WR| rewrite !shad_div; lia| rewrite !shad_div; lia| rewrite !shad_div; lia]
                                               | unfold app_blk, KLOW; lia]]].
  destruct SB as (_ & _ & SB). split; [lia|]. split; [lia|].
  intros G Hlt Hlo Hhi. exists (Z_to_bv 8 0). split.
  - apply SB. rewrite !shad_div. change ASHOFF with 0x7fff8000. lia.
  - left. reflexivity.
Qed.

Lemma rodata_sh0_fmt : forall m A n, rodata_sh0 m -> 0x10000 + 64 <= A -> 0 <= n -> A + n + 64 <= 0x20dc0 ->
  shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0).
Proof.
Proof.
  intros m A n [SB _] H1 H2 H3. eapply shadow_bytes_sub; [exact SB | |]; apply shad_mono; lia.
Qed.

Lemma rodata_sh0_frame : forall W m m', rodata_sh0 m -> munch W m m' -> wmono bsegs m m' -> appW W -> rodata_sh0 m'.
Proof.
  intros W m m' [SB [WR HBM]] MU WM AW. split; [| split].
  - eapply shadow_bytes_munch; [exact SB | exact MU |].
    pose proof (appW_shadow_disjoint W 0x10000 0x20dc0 AW ltac:(lia) ltac:(unfold KEND; lia)) as D. exact D.
  - eapply wr_at_transport; [exact WR | exact WM].
  - eapply hinv_bm_munch; [exact HBM | exact MU | exact AW].
Qed.

(* [comment removed for export] *)
Definition rrng_fmt (RNG : footprint) : Prop := rrng RNG RFMT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition drv_img_ranges : list (Z * Z) :=
  [(0x10000, 0x20dc0);                      (* [comment removed for export] *)
   (0x5ec950, 0x5ec980);                    (* [comment removed for export] *)
   (RSTDERR, RSTDERR + 232); (RSTDOUT, RSTDOUT + 232); (0xb67e0, 0xb67e8); (0xb68d0, 0xb68d8); (0xb69c0, 0xb69c8);
   (0x60d980, 0x60ddc0);                    (* [comment removed for export] *)
   (0x5ed1e8, 0x5ed1f0); (0x60d2d0, 0x60d2d8); (0x60d2e0, 0x60d310); (0x60d400, 0x60d410); (0x60d500, 0x60d508);
   (0x60d520, 0x60d530);                    (* [comment removed for export] *)
   (0xb69f0, 0xb6c30); (0xb6c40, 0xb6c48); (0xb6c90, 0xb6c91); (0xb3e40, 0xb3e48);
                                            (* [comment removed for export] *)
   (0x14c1a0, 0x14c1a1); (0xb7b10, 0xb7b14); (0xb7bb0, 0xb7bb8); (* [comment removed for export] *)
   (0x20e00, 0x21280);                      (* [comment removed for export] *)
   (0xb68d8, 0xb6968);                    (* [comment removed for export] *)
   (0x5dc940, 0x5ec980)]%Z.                (* [comment removed for export] *)

(* [comment removed for export] *)
Definition cli_img_ranges : list (Z * Z) := [].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aat_exit (code : Z) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
  exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo t : Z) (cdt thr sec : byte) (tm1 dso guard : word),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AEXIT_PC) fc None m (seg_rom bsegs)
    /\ mdtor_pre m
    /\ stk bsegs m lo (bv_unsigned sp)
    /\ rw_cells bsegs m 0x5ed1e8 [C4 (Z_to_bv 64 t)]
    /\ rw_cells bsegs m 0x60d500 [C4 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m 0x60d520 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ (exists reg : bool, atx_stateA reg m)            (* [comment removed for export] *)
    /\ rw_cells bsegs m 0xb2e00 [C8 (Z_to_bv 64 0xb1bc0); C8 (Z_to_bv 64 0xb1bb0)]
    /\ rw_cells bsegs m 0xb1bb0 [C8 (Z_to_bv 64 0x969cc); C8 (Z_to_bv 64 0x3072c)]
    /\ rw_cells bsegs m 0xb6c90 [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m 0xb20f8 [C8 (Z_to_bv 64 0xa1b28); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m 0xb3e40 [C8 dso]
    /\ rw_cells bsegs m 0x60d988 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0xb69c0 [C8 (Z_to_bv 64 RSTDIN)] /\ rw_cells bsegs m RSTDIN stdin_cells
    /\ rw_cells bsegs m 0xb68d0 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells bsegs m 0xb67e0 [C8 (Z_to_bv 64 RSTDERR)]
    /\ stdout_file m (aps_so s) /\ stderr_file m
    /\ rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells bsegs m ssp_guard [C8 guard]
    /\ mem_inv bsegs m
    /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code
    /\ 0 < t < 4194304 /\ lo <= bv_unsigned sp - 48 - MDTOR_DEPTH /\ KHIGH <= lo
    /\ rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W /\ rng0 RNG
    /\ bv_unsigned sp < 2^47.                                    (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma aps_get_set' : forall (s : APS) so, aps_so (aset_so so s) = so.
Proof.
ltac2:(KReplay.run1 (kr_t_ADriver_iface ()) ["CANSEC1"] "h01sh12sop;2g003^j20Tg01NYg01OUR0f0,00W1W0o"). Qed.
Lemma aps_set_set' : forall (s : APS) so so', aset_so so' (aset_so so s) = aset_so so' s.
Proof.
ltac2:(KReplay.run1 (kr_t_ADriver_iface ()) ["CANSEC1"] "h01sh12soh23so'p;2g01PPj21Tg003^j20Tg01NYR0g01OUR1f0f2'1,00X21W1W0o"). Qed.
Lemma aps_set_get' : forall (s : APS), aset_so (aps_so s) s = s.
Proof.
ltac2:(KReplay.run1 (kr_t_ADriver_iface ()) ["CANSEC1"] "p'0h01ai001ah18aps_atopi018aps_atoph28aps_resvi028aps_resvh31bh41si035aps_mi046aps_sop;1p;2p;3p;4g01QNj16Tg01PPj25Tg001Kj30Tg01RKj21Tg00Sij14Tg01Rkj42Tg003^j23Tg01NYR0P0f0R1#6/51=001P1g01Sgg01OUg0066R2/12#4f3R3f2R4f1R5P1C2,30X12W2W3W0P3P4P5P1O4n01100000140103104102101W4o"). Qed.

(* [comment removed for export] *)
Lemma aexit_from_aat_exit : forall code (s : APS) RNG ms (Q : Empty_set -> APS -> footprint -> machine_state -> Prop),
  aat_exit code s RNG ms -> implMA RNG (exit_model (ioA AAllocAsan) code) s Q ms.
Proof.
  intros code s RNG ms Q H. unfold aat_exit in H.
  repeat match type of H with ex _ => let x := fresh "x" in destruct H as [x H] end.
  repeat match type of H with _ /\ _ => let h := fresh "C" in destruct H as [h H] end.
  subst ms.
  repeat match goal with C : ex _ |- _ => let x := fresh "x" in destruct C as [x C] end.
  unfold implMA. change (ioA AAllocAsan) with (io_S (St := APS) aps_so aset_so).
  eapply implF_epost_mono.
  - eapply (aexit_spec_closed aps_so aset_so aps_get_set' aps_set_set' aps_set_get' _ RNG s (fun (e : Empty_set) _ _ => match e with end));
      eassumption.
  - intros [e ?] RNG' ms'. destruct e.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma atarget_alloc_init_spec : forall RNG (bitmap : Z) (s : APS)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem),
  implMA RNG (alloc_initA AAllocAsan bitmap) s
        (fun _ s' RNG' ms' => RNG' = RNG /\ s' = s /\
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m (seg_rom bsegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ATARGET_ALLOC_INIT) fc None m (seg_rom bsegs)).
Proof.
  intros. unfold alloc_initA, Adapter.target_alloc_init, ATARGET_ALLOC_INIT. apply implMA_ret.
  step. apply evtF_done. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma atarget_alloc_count_spec : forall RNG (s : APS)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem),
  implMA RNG (alloc_countA AAllocAsan) s
        (fun r s' RNG' ms' => RNG' = RNG /\ s' = s /\ r = 0 /\
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m (seg_rom bsegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ATARGET_ALLOC_COUNT) fc None m (seg_rom bsegs)).
Proof.
  intros. unfold alloc_countA, Adapter.target_alloc_count, ATARGET_ALLOC_COUNT. apply implMA_ret.
  step. step. apply evtF_done. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DrvStmts.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  (* [comment removed for export] *)

  Definition dmalloc_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
      (r : astate * option AsanCtrl.aptr) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m' /\ astk_shadow_pres (bv_unsigned sp) m m'
      /\ match snd r with
         | None => False
         | Some p => exists A junk,
             a0 = Z_to_bv 64 A /\ ablock_range A n
             /\ AHEAP AI L RNG' (fst r) (HB p A n :: LB) m'
             /\ rw_cells bsegs m' A [CB (Z.to_nat n) junk]
             /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7))
             /\ (is_primary n = false -> A = AsanCtrl.aptr_addr (fst r) p)
         end.

  Definition dmalloc_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (RESV : list (Z * Z)),
      AHEAP AI L RNG st LB m -> mem_inv bsegs m ->
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
      tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
      bv_unsigned s0 <= bv_unsigned sp -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC -> bv_unsigned sp mod 16 = 0 ->
      In [AMALLOC_PC; bv_unsigned ra] (al_U L) -> In [AMALLOC_PC] (al_U L) ->
      rng RNG lo (al_top L - lo) ->
      bv_unsigned sp < 2^47 -> rng RNG lo (bv_unsigned sp - lo) ->      (* [comment removed for export] *)
      aresv_ok L RESV ->                                            (* [comment removed for export] *)
      implS bsegs RNG (aembed ATOP (AsanCtrl.amalloc ATOP RESV st n))
            (epostF (dmalloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).

  Definition dfree_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : astate) (LB : list ablock) (p : AsanCtrl.aptr) (lo : Z) (m : amem)
      (r : astate) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m' /\ astk_shadow_pres (bv_unsigned sp) m m'
      /\ AHEAP AI L RNG' r (lb_remove p LB) m'.

  Definition dfree_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z),
      AHEAP AI L RNG st LB m -> In (HB p A n) LB -> mem_inv bsegs m ->
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
      tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 A ->
      bv_unsigned s0 <= bv_unsigned sp -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> bv_unsigned sp mod 16 = 0 ->
      In [AFREE_PC; bv_unsigned ra] (al_U L) -> In [AFREE_PC] (al_U L) ->
      rng RNG lo (al_top L - lo) ->
      bv_unsigned sp < 2^47 -> rng RNG lo (bv_unsigned sp - lo) ->      (* [comment removed for export] *)
      implS bsegs RNG (aembed ATOP (AsanCtrl.afree st (Some p)))
            (epostF (dfree_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).

  Definition dfree_null_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m' /\ astk_shadow_pres (bv_unsigned sp) m m'
      /\ AHEAP AI L RNG st LB m'.

  Definition dfree_null_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
      AHEAP AI L RNG st LB m -> mem_inv bsegs m ->
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
      tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 0 ->
      bv_unsigned s0 <= bv_unsigned sp -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> bv_unsigned sp mod 16 = 0 ->
      In [AFREE_PC; bv_unsigned ra] (al_U L) -> In [AFREE_PC] (al_U L) ->
      rng RNG lo (al_top L - lo) ->
      bv_unsigned sp < 2^47 -> rng RNG lo (bv_unsigned sp - lo) ->      (* [comment removed for export] *)
      evtF bsegs RNG (dfree_null_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition ashenv_law : Prop := forall L RNG st LB m, AHEAP AI L RNG st LB m -> ashenv m.

  (* [comment removed for export] *)
  Lemma ashenv_law_holds : ashenv_law.
Proof.
    intros L RNG st LB m AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. unfold artcells in RT. decompose [and] RT.
    unfold ashenv. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma dmalloc_M : dmalloc_stmt -> forall (L : alayout) (RNG : footprint)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (n lo : Z),
    AHEAP AI L RNG (aps_m s) LB m -> mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
    bv_unsigned s0 <= bv_unsigned sp -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC -> bv_unsigned sp mod 16 = 0 ->
    In [AMALLOC_PC; bv_unsigned ra] (al_U L) -> In [AMALLOC_PC] (al_U L) ->
    rng RNG lo (al_top L - lo) ->
    bv_unsigned sp < 2^47 -> rng RNG lo (bv_unsigned sp - lo) ->      (* [comment removed for export] *)
    aps_ok L s ->
    implMA RNG (amalloc_M n) s
      (fun r s' RNG' ms' => aps_rest s' = aps_rest s
         /\ dmalloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (aps_m s) LB n lo m (aps_m s', r) RNG' ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).
  Proof.
    intros DM. intros. lazymatch goal with H : aps_ok _ _ |- _ => destruct H as [HRV HAT] end.
    apply implMA_amalloc; [exact HAT|]. eapply implF_epost_mono; [eapply DM; eauto|].
    cbv beta. intros [st' r] RNG' ms' PO. split; [reflexivity| exact PO].
  Qed.

  Lemma dfree_M : dfree_stmt -> forall (L : alayout) (RNG : footprint)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z),
    AHEAP AI L RNG (aps_m s) LB m -> In (HB p A n) LB -> mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 A ->
    bv_unsigned s0 <= bv_unsigned sp -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> bv_unsigned sp mod 16 = 0 ->
    In [AFREE_PC; bv_unsigned ra] (al_U L) -> In [AFREE_PC] (al_U L) ->
    rng RNG lo (al_top L - lo) ->
    bv_unsigned sp < 2^47 -> rng RNG lo (bv_unsigned sp - lo) ->      (* [comment removed for export] *)
    aps_ok L s ->                                                 (* [comment removed for export] *)
    implMA RNG (afree_M p) s
      (fun _ s' RNG' ms' => aps_rest s' = aps_rest s
         /\ dfree_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (aps_m s) LB p lo m (aps_m s') RNG' ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
  Proof.
    intros DF. intros. lazymatch goal with H : aps_ok _ _ |- _ => destruct H as [HRV HAT] end.
    apply implMA_afree; [exact HAT|]. eapply implF_epost_mono; [eapply DF; eauto|].
    cbv beta. intros st' RNG' ms' PO. split; [reflexivity| exact PO].
  Qed.

  (* [comment removed for export] *)
  Lemma aunw_drv : forall m L RNG lo PC (sp s0 ra : word),
    bv_unsigned s0 <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
    In [PC; bv_unsigned ra] (al_U L) -> In [PC] (al_U L) -> rng RNG lo (al_top L - lo) ->
    aunw m L RNG lo PC sp s0 ra [].
  Proof.
    intros m L RNG lo PC sp s0 ra Hs0 Hsp U2 U1 R. unfold aunw.
    destruct (Z.lt_ge_cases (bv_unsigned sp + 16) (al_top L)) as [LT|GE].
    - left. split; [exact LT|]. split; [apply uc_stop; lia|]. split; [cbn; lia|]. split; [exact U2| exact R].
    - right. split; [lia|]. split; [exact Hsp| exact U1].
  Qed.

  Lemma astk_shadow_pres_of_aheap_pres : forall LB (sp : Z) m m',
    aheap_pres CI LB sp m m' -> sp <= 2^47 -> astk_shadow_pres sp m m'.
  Proof.
    intros LB sp m m' HP Hsp a Ha. unfold shad, AsanEmbed.ASHOFF in Ha. rewrite !Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha.
    destruct (HP a) as [E _]; [lia| | exact E].
    right. right. right. exists (8 * (a - 2147450880)). split.
    - left. atop_facts. pose proof ATOP_al16. Z.div_mod_to_equations. lia.
    - unfold shad, AsanEmbed.ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. pose proof ATOP_al16. Z.div_mod_to_equations. lia.
  Qed.

  Theorem dmalloc_of_AI : dmalloc_stmt.
  Proof.
    unfold dmalloc_stmt. intros until RESV. intros AH MI ST BOT LO TP A0 N S0 RA RA' SP16 U2 U1 RT SP47 RS ROK.
    eapply implF_epost_mono.
    - eapply (AI_malloc AI) with (tr := []); try eassumption.
      + apply aunw_drv; assumption.
      + lia.
    - cbv beta. intros [st' r] RNG' ms' (LE & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & HP & RR).
      split; [exact LE|]. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HP|].
      split; [eapply astk_shadow_pres_of_aheap_pres; [exact HP| lia]| exact RR].
  Qed.

  Theorem dfree_of_AI : dfree_stmt.
  Proof.
    unfold dfree_stmt. intros until lo. intros AH IN MI ST BOT LO TP A0 S0 RA RA' SP16 U2 U1 RT SP47 RS.
    eapply implF_epost_mono.
    - eapply (AI_free AI) with (tr := []); try eassumption.
      + apply aunw_drv; assumption.
      + lia.
    - cbv beta. intros st' RNG' ms' (LE & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & HP & AH').
      split; [exact LE|]. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HP|].
      split; [eapply astk_shadow_pres_of_aheap_pres; [exact HP| lia]| exact AH'].
  Qed.

  Theorem dfree_null_of_AI : dfree_null_stmt.
  Proof.
    unfold dfree_null_stmt. intros until lo. intros AH MI ST BOT LO TP A0 S0 RA RA' SP16 U2 U1 RT SP47 RS.
    eapply evtF_mono.
    - eapply (AI_free_null AI) with (tr := []); try eassumption.
      + apply aunw_drv; assumption.
      + lia.
    - cbv beta. intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & HP & AH').
      exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HP|].
      split; [eapply astk_shadow_pres_of_aheap_pres; [exact HP| lia]| exact AH'].
  Qed.
End DrvStmts.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TargetRun.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  (* [comment removed for export] *)
  Definition atrun_cells0 (m : amem) : Prop :=
    rw_cells bsegs m AINIT_FLAG [C1 (Z_to_bv 8 0)] /\ atx_stateA false m.

  Definition atrun0_addrA (a : Z) : Prop := (AINIT_FLAG <= a < AINIT_FLAG + 1) \/ atx_state_addrA a.

  Lemma atrun_cells0_magree : forall (P : Z -> Prop) m m',
    magree bsegs P m m' -> (forall a, atrun0_addrA a -> P a) -> atrun_cells0 m -> atrun_cells0 m'.
Proof.
    intros P m m' AG HP [C1 AX]. split.
    - eapply rw_cells_magree; [exact AG | exact C1 |].
      intros a Ha. apply HP. left. cbn in Ha. lia.
    - eapply atx_stateA_agree; [exact AG | | exact AX].
      intros a Ha. apply HP. right. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Definition atrun_ivs : list (Z * Z) :=
    [(RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024); (AINIT_FLAG, AINIT_FLAG + 1);
     (0x5ec954, 0x5ec955); (0x60d2e8, 0x60d2ec); (0x60d308, 0x60d310); (0x60d408, 0x60d410)].

  Fixpoint rin_ivs (ivs : list (Z * Z)) (a : Z) : Prop :=
    match ivs with [] => False | (lo, hi) :: ivs' => (lo <= a < hi) \/ rin_ivs ivs' a end.

  (* [comment removed for export] *)
  Definition adrv_pres (LB : list ablock) (SP : Z) (m m' : amem) : Prop :=
    forall a, 0 <= a < 2^64 -> (aclient_addr CI LB SP a \/ (shad ATOP <= a < shad SP)) -> ~ rin_ivs atrun_ivs a ->
      m' (wa a) = m (wa a) /\ (wview bsegs m (wa a) <> None -> wview bsegs m' (wa a) <> None).

  Lemma adrv_pres_refl : forall LB SP m, adrv_pres LB SP m m.
  Proof. intros LB SP m a _ _ _. auto. Qed.

  Lemma adrv_pres_trans : forall LB SP m1 m2 m3, adrv_pres LB SP m1 m2 -> adrv_pres LB SP m2 m3 -> adrv_pres LB SP m1 m3.
Proof.
    intros LB SP m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
    split; [congruence| auto].
  Qed.

  (* [comment removed for export] *)
  Definition atarget_run_postA (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : APS) (LB : list ablock) (lo : Z) (canary : word) (m : amem)
      (r : Z) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ 0 <= r <= 2
      /\ mem_inv bsegs m' /\ frm0 fc' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ adrv_pres LB (bv_unsigned sp) m m'
      /\ AHEAP AI L RNG' (aps_m s') LB m'
      /\ stdout_file m' (aps_so s')
      /\ ssp_cells m' canary
      /\ atx_stateA true m'                                      (* [comment removed for export] *)
      /\ aps_ok L s'.                                            (* [comment removed for export] *)

  Variable rng_fs : alayout -> footprint -> Prop.

  (* [comment removed for export] *)
  Definition atarget_run_stmtA : Prop :=
    forall (L : alayout) (RNG : footprint) (rstk : region)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A cap Lc : Z) (content : list Z) (lo : Z) (canary : word),
      AHEAP AI L RNG (aps_m s) LB m -> In (HB p A cap) LB -> (forall b, In b LB -> exists p' A' n', b = HB p' A' n') ->
      bytes_at bsegs m A (map (Z_to_bv 8) content) -> Forall (fun c => 0 <= c < 256) content ->
      zlength content <= cap -> cap <= 2^26 -> 0 <= Lc -> 6 + Lc <= zlength content ->
      atrun_cells0 m -> harness_invA m ->
      (exists (cdt thr sec : byte) (tm1 : word), rw_cells bsegs m 0x60d520 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]) ->   (* [comment removed for export] *)
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ATARGET_RUN_STACK ->
      bv_unsigned sp + 128 = al_sp0 L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^47 ->     (* [comment removed for export] *)
      mem_inv bsegs m -> frm0 fc ->
      stdout_file m (aps_so s) -> ssp_cells m canary ->
      aps_ok L s ->                                   (* [comment removed for export] *)
      (* [comment removed for export] *)
      rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk -> rodata_sh0 m -> rclean m RBstdout ->
      tp = Z_to_bv 64 ATP ->
      a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 Lc -> a2 = Z_to_bv 64 (A + 6 + Lc) -> a3 = Z_to_bv 64 (zlength content - 6 - Lc) ->
      (* [comment removed for export] *)
      HU L -> In [AMALLOC_PC; 0x7fe20] (al_U L) -> In [AFREE_PC; 0x7feb4] (al_U L) -> In [AMALLOC_PC] (al_U L) -> In [AFREE_PC] (al_U L) ->
      (* [comment removed for export] *)
      rng RNG lo (bv_unsigned sp + 128 - lo) -> rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
      rrng RNG rstk -> rrng RNG RFMT -> rrng RNG RBstdout ->
      implMA RNG (runA AAllocAsan (if 0 <? Lc then znth content 2 else 0) (skipn (Z.to_nat (6 + Lc)) content)) s
             (atarget_run_postA L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo canary m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 ATARGET_RUN) fc None m (seg_rom bsegs)).
End TargetRun.
End CANSEC1.
