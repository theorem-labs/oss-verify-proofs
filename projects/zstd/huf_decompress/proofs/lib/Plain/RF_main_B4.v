(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (1 recorded proof replaced by written proofs (main_read_all); open's TASK_SIZE premise and the zero-mapped stack depth; zstd/simple_decompress's proof, with this binary's addresses). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem MonadX.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg F_syscalls F_memcpy StdioFiles Startup Exit F_printf_iface Stdio_iface Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B2 RF_main_B3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_main_B4 () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalI47Corelib5Lists7ListDef6Forall00C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver8read_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;Stdio_iface@fwrite_diag_postC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface@emit_printf_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocI59OSSVerify5KrLib4Spec6Driver9rd_result00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RF_main_B1<fprintf_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RF_main_B1;fwrite_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List9nth_errorK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5Plain;RDriver_ctx6MFRAMEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9RF_main_A4BASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image9reservedZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState7ps_initC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib5Plain=RMalloc_iface5RHEAPC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9RF_main_A3STGC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib6Common;Startup_kit9envp_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyK47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5Plain;RDriver_ctx8sp_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib5Plain;RDriver_ctx2LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9RF_main_A8IMGB_lenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib5Plain;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RDriver_ctx5RSTATC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Harness_iface<stderr_file0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RDriver_iface;trun_cells0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5Plain;RDriver_kit<argv_cstringC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem9argv_ptrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem8str_baseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib5Plain;RDriver_kit<stack_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem4argcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem9envp_ptrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem4envcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem:auxv_wordsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?flatten_stringsC59OSSVerify5KrLib3Lib7InitMem8env_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem8rnd_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem9rnd_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RDriver_kit9RHEAP_sspC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapK59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps:raw_mallocC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver5rd_st00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib5Plain:RF_main_B45POSTBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib7InitMem@argv_ptrs_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_app1C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree:u64ro_readC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib6Common8DrvAgreeDzbytes_map_unsigned'C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib5Plain:F_syscalls9open_postC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib5Plain:F_syscalls9open_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RDriver_kit>implM_of_enodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls8open_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addI47Corelib4Init5Logic2or00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C46Stdlib5Lists4List:length_appC59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib5Plain9RF_main_A3WOKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9RF_main_A<RHEAP_munchWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9RF_main_A:BASE_munchC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode4sret01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain8F_atexit9atx_stateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr05C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib3Lib7ZBridge=bv_lts_zero_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree@map_unsigned_posC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5Plain9RF_main_A8IMGB_topC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5Plain>F_printf_iface9diag_argsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RDriver_iface8pat_exitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtK59OSSVerify5KrLib3Lib6Decode4sret02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C59OSSVerify5KrLib3Lib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5b_luiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface<rmalloc_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface<rblock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface=raddr_exposedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface:rheap_presC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9RF_main_A>BASE_heap_presC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib5Plain=RMalloc_ifaceCrheap_pres_rw_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib5Plain:RF_main_B38POSTLOOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RF_main_B13BUFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RF_main_B15STAGEC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib6Common:Stdio_pure<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RF_main_B2<rw_cells_CB0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec6Driver:rd_contentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6rd_capC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6rd_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RF_main_B15RDINVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RF_main_B37rd_loopC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls:close_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls:close_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls9close_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls;close_errnoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RF_main_B45RDONEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles;stdout_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver>read_loop_bodyC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver5rd_st01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result02C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib5Plain:F_syscalls:open_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps8ptr_addrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep6RERRNOC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog2ioC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps8raw_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg;PREAD_STAGEC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5Plain:F_syscalls7got_sspC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode4sret00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode9dec_closeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib5Plain7RunDraw:PSTAGE_LENC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9MAX_INPUTC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Plain:RMallocRep4RATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain7RunDraw<PSTAGE_LEN_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg7p_phdrsC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathI47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib4Spec6Driver9READ_FUELC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg04C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib5Plain=RDriver_iface5PMAINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RDriver_iface;PSTAGE2_RETC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C59OSSVerify5KrLib6Common;Printf_fmtsAA_FMT_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles;GLOBALS_TOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface=RMALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep5RLIBCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ua := idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT} {lx : launchT}.
Section B4.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (J8 : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : dvalid_sp sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TOW : towrite_stmt.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes L_LA pph (Z_to_bv 64 (Z.of_N p_init_pc)) sp0 L_TOP argv envp L_EXECFN uid L_GID hw draw).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw draw TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm J8 S7 S6 S5 S4).
  Notation RDINV' := (RDINV sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).
  Notation RDBRK' := (RDBRK sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).
  Notation POSTLOOP' := (POSTLOOP sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).
  Ltac hyps := first [exact VSP | exact VARGV | exact VENVP | exact EARGV | exact HT | exact MALLOC | exact FREE | exact FPR | exact FWX | exact SWF | exact FWR | exact TOW].

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 PREAD_STAGE) x23 t3 t4 t5 t6 F fc mm).

  (* [comment removed for export] *)
  Definition RDONE (bufp : bptr) (content : list Z) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A cap P1v fd : Z) (DATA junk : list byte) (errv : word),
      ms = RST 0x12e2c x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF mm s bufp A cap DATA junk
      /\ FRAME' mm /\ BASE' mm /\ rw_cells psegs mm RERRNO [C4 errv] /\ frm0 fc.

  Definition POSTB (r : rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | RdExit => pat_exit 2 s ms
    | RdDone b c => RDONE b c s ms
    end.

  Lemma main_read_all : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mm : mem),
    FRAME' mm -> BASE' mm -> RHEAP (ps_init (reservedZ psegs) ATOP) [] mm -> rw_cells psegs mm RERRNO [C4 (Z_to_bv 64 0)] -> frm0 fc -> STG mm ->
    implM psegs (read_all Prog.io raw_malloc raw_free PREAD_STAGE (map bv_unsigned arg1)) (ps_init (reservedZ psegs) ATOP) POSTB
      (MS (mkR (Z_to_bv 64 0x1d368) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
               (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
               (Z_to_bv 64 0x12d30) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          bvmap_empty (Z_to_bv 64 0x12d60) fc None mm (seg_rom psegs)).
  Proof.
    intros until mm. intros FR BA HP0 ERR FRM [sj SJ]. unfold PREAD_STAGE in SJ. pose proof PSTAGE_LEN_Z as PSTAGER.
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF. pose proof (IMGB_len sp0 argv envp uid hw draw VSP VARGV VENVP) as IL.
    pose proof (IMGB_top sp0 argv envp uid hw draw VSP) as ITOP.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
    pose proof VARGV as (_ & _ & ARGLEN & NONUL & NOSL).
    (* [comment removed for export] *)
    destruct (argv_cstring sp0 argv envp uid hw draw mm IMG (dvalid_padok _ _ _ VSP) 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
      as (P1v & slack1 & HP1 & P1LO & P1HI & STR1 & SLK1).
    pose proof (layout_bounds L_LA sp0 L_TOP argv envp L_EXECFN (dvalid_padok _ _ _ VSP)) as (LBS & _).
    pose proof (Nat2Z.is_nonneg (block_head_size (la_rseq L_LA) argv envp)). unfold hsz in LBS.
    destruct (stack_pieces sp0 argv envp uid hw draw mm IMG (dvalid_padok _ _ _ VSP)) as (_ & ARGVP & _).
    assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
    assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
    assert (A1NOSL : path_has_slash arg1 = false) by (rewrite EARGV in NOSL; cbn [tl] in NOSL; inversion NOSL as [|? ? [X _]]; exact X).
    assert (STR1' : bytes_at psegs mm P1v (arg1 ++ [Z_to_bv 8 0])).
    { change (arg1 ++ Z_to_bv 8 0 :: slack1) with (arg1 ++ ([Z_to_bv 8 0] ++ slack1)) in STR1. rewrite app_assoc in STR1. apply bytes_at_app in STR1. destruct STR1 as [S1 _]. exact S1. }
    pose proof (RHEAP_ssp _ _ _ HP0) as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2.
    unfold read_all. unfold implM. iprefix.
    pose proof (u64ro_read psegs mm (usp0 + 8) (argv_ptrs L_TOP argv envp L_EXECFN ++ [Z_to_bv 64 0]) 1 (Z_to_bv 64 P1v) (Z_to_bv 64 (usp0 + 16))
                  ARGVP ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP1) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep.
    remember READ_FUEL as rf eqn:Erf. clear Erf.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm (ps_init (reservedZ psegs) ATOP) POSTB msx) end.
    replace (map (Z_to_bv 8) (map bv_unsigned arg1)) with arg1 by (symmetry; apply zbytes_map_unsigned').
    eapply implM_bind.
    { eapply implM_of_enode.
      eapply open_spec with (lo := usp0 - 6144513) (errv := Z_to_bv 64 0) (canary := CAN);
        [ rewrite (unsigned_lit (usp0 + -128)) by lia; exact ST
        | rewrite (unsigned_lit P1v) by lia; exact STR1'
        | unfold RATP; rewrite (unsigned_lit 227376) by lia; exact ERR
        | exact G1 | exact G2 | exact MI | reflexivity | exact A1NN | exact A1NOSL | ..].
      all: unfold RATP, F_syscalls.got_ssp, F_syscalls.ssp_guard; rewrite ?TASK_SIZE_val; rewrite ?(unsigned_lit 227376) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit P1v) by lia; lia. }
    cbv beta. intros r s' ms' [PO ->].
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & ERR1 & _ & _ & _ & FDR).
    unfold RATP in MUc, ERR1. rewrite ?(unsigned_lit 227376) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit 227376) in ERR1 by lia. change (227376 + -164) with 227212 in MUc, ERR1.
    transport_after_call psegs mm m1 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x12d70)) with (Z_to_bv 64 0x12d70) by (symmetry; rpc).
    assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 112, usp0 + -128); (227212, 227212 + 4)]).
    { unfold WOK, LO, RERRNO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (HP1' : RHEAP (ps_init (reservedZ psegs) ATOP) [] m1).
    { eapply (RHEAP_munchW sp0 argv envp VSP); [exact WOKW| exact MUc| exact WMc| | exact HP0]. intros iv [<-|[<-|[]]]; cbn [fst snd]; atop_facts; intros; lia. }
    assert (BA1 : BASE' m1) by (eapply (BASE_munch sp0 argv envp uid hw draw TID VSP VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI1| unfold LO; first [exact ST1| replace (usp0 - 6144513) with (usp0 + -6144513) by lia; exact ST1]]).
    clear MUc WMc BA WOKW HP0 G1 G2. try clear ST. try clear MI. try clear RS. try clear AUX. try clear IMG. try clear SE. try clear SOF. try clear TR.
    pose proof BA1 as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST.
    unfold implM. iprefix.
    destruct r as [e|fd]; cbn [open_ret open_errno] in *.
    - (* [comment removed for export] *)
      pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _).
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm (ps_init (reservedZ psegs) ATOP) POSTB msx) end.
      cbn [io_diag io_S].
      eapply (fprintf_exit sp0 argv envp uid hw draw TID S8 S9 S10 S11 VSP HT FPR FWX SWF (DCannotOpen (map bv_unsigned arg1)));
        [| exact BA1| exact HP1'| reflexivity| exact FRM| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
      unfold F_fmt_fp_lib.zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
      split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
      split; [unfold FmtFp.INT_MAX; lia|]. split; [right; lia|]. split; [unfold GLOBALS_TOP; lia|].
      pose proof (IMGB_top sp0 argv envp uid hw draw VSP). lia.
    - (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; try (exfalso; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm (ps_init (reservedZ psegs) ATOP) POSTB msx) end.
      eapply implM_bind.
      { unfold rmalloc_stmt in MALLOC.
        eapply MALLOC with (lo := usp0 - 6144513) (B := usp0); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 227376) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
          first [ exact HP1' | exact AUX | exact ST | exact ERR1 | exact MI | unfold RMALLOC_STACK; lia | lia ]. }
      cbv beta. intros r s1 ms1 PO.
      destruct PO as (v0 & v1 & v2 & ra0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
      unfold RATP in ERR2. rewrite ?(unsigned_lit 227376) in ERR2 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
      change (227376 + -164) with 227212 in ERR2.
      replace (ret_pc (Z_to_bv 64 0x12d84)) with (Z_to_bv 64 0x12d84) by (symmetry; rpc).
      assert (BA2 : BASE' m2) by (eapply (BASE_heap_pres sp0 argv envp uid hw draw TID); [exact BA1| exact HPR| exact MI2| unfold LO; first [exact ST2| replace (usp0 - 6144513) with (usp0 + -6144513) by lia; exact ST2]| exact AUX2]).
      assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
      assert (SJ2 : rw_cells psegs m2 161577 [CB PSTAGE_LEN sj]).
      { eapply rheap_pres_rw_cells; [exact HPR| exact SJ|]. right; left. cbn [cells_size csize Nat.add]. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
      clear FR ST MI RS AUX IMG SE SOF ERR1 TR SJ.
      pose proof BA2 as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST.
      unfold implM. iprefix.
      destruct r as [buf|].
      2:{ (* [comment removed for export] *)
          destruct RR as [-> HEAP2].
          pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _).
          zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.
          zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
          lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s1 POSTB msx) end.
          cbn [io_diag io_S].
          eapply (fwrite_exit sp0 argv envp uid hw draw TID S8 S9 S10 S11 VSP HT FWR TOW);
            [exact BA2| exact HEAP2| rewrite SOE; reflexivity| intros ms'' AE; apply implM_ret; apply evt_done; exact AE]. }
      destruct RR as (A & junk & -> & BR & HEAP2 & BLK & HEXP).
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts.
      zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s1 POSTB msx) end.
      eapply implM_bind.
      { apply (rd_loop sp0 argv envp uid hw draw arg0 arg1 TID J8 S4 S5 S6 S7 S8 S9 S10 S11 VSP VARGV VENVP EARGV HT MALLOC FREE FPR FWX SWF FWR TOW rf fd P1v); [lia| exact HP1|].
        unfold RDINV. cbn [rd_content rd_cap rd_buf zlength length Z.of_nat].
        do 17 eexists. exists bvmap_empty, fc, m2, A, [], junk, errv2, sj, 0x12d98.
        split; [unfold PREAD_STAGE; reflexivity|]. split; [right; split; reflexivity|]. split; [reflexivity|].
        split; [| split; [exact SJ2| split; [exact FR2| split; [exact BA2| split; [exact ERR2| exact FRM]]]]].
        split; [exact HEAP2|]. split; [rewrite FAE; reflexivity|]. split; [rewrite SOE; reflexivity|]. split; [exact I|]. cbn [length Z.of_nat Z.sub].
        split; [replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by reflexivity; apply (proj2 (rw_cells_app _ _ _ [CB 0%nat []] _)); split; [| cbn [cells_size csize Nat.add]; rewrite Z.add_0_r; exact BLK] |].
        - apply rw_cells_CB0. lia.
        - unfold MAX_INPUT. split; [split; [lia| exists 16; split; [lia| reflexivity]]|]. split; [lia| exact BR]. }
      cbv beta. intros res s2 ms2 PO.
      destruct res as [|b c]; cbn [POSTLOOP] in PO.
      { apply implM_ret. apply evt_done. exact PO. }
      (* [comment removed for export] *)
      clear dependent m2.
      destruct PO as (x1 & w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & x23 & F2 & fc2 & m3 & A3 & cap3 & DATA3 & junk3 & errv3
                      & -> & HC3 & BU3 & FR3 & BA3 & ERR3 & FRM3).
      pose proof BA3 as (ST & MI & RS & AUX & IMG & SE & SOF & TR3). unfold LO in ST. unfold RERRNO in ERR3. unfold MFRAME in FR3.
      pose proof BU3 as (P3 & FA3 & SO3 & HA3 & BLK3 & CAP3 & LEN3 & BRR3).
      pose proof BRR3 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). atop_facts.
      unfold implM. iprefix. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s2 POSTB msx) end.
      eapply implM_bind.
      { eapply implM_of_enode.
        eapply close_spec with (lo := usp0 - 6144513) (errv := errv3); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 227376) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
          first [ exact ST | exact ERR3 | exact MI | lia ]. }
      cbv beta. intros r3 s3 ms3 [PO ->].
      destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m4 & -> & MUc & WMc & MI4 & ST4 & ERR4).
      unfold RATP in MUc, ERR4. rewrite ?(unsigned_lit 227376) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST4 by lia. rewrite ?(unsigned_lit 227376) in ERR4 by lia. change (227376 + -164) with 227212 in MUc, ERR4.
      transport_after_call psegs m3 m4 MUc WMc.
      replace (ret_pc (Z_to_bv 64 0x12e2c)) with (Z_to_bv 64 0x12e2c) by (symmetry; rpc).
      assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 32, usp0 + -128); (227212, 227212 + 4)]).
      { unfold WOK, LO, RERRNO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
      assert (P4 : RHEAP s2 [(b, A3, cap3)] m4).
      { eapply (RHEAP_munchW sp0 argv envp VSP); [exact WOKW| exact MUc| exact WMc| | exact P3]. intros iv [<-|[<-|[]]]; cbn [fst snd]; atop_facts; intros; lia. }
      assert (BA4 : BASE' m4) by (eapply (BASE_munch sp0 argv envp uid hw draw TID VSP VARGV VENVP); [exact BA3| exact WOKW| exact MUc| exact WMc| exact MI4| unfold LO; first [exact ST4| replace (usp0 - 6144513) with (usp0 + -6144513) by lia; exact ST4]]).
      apply implM_ret. apply evt_done. cbn [POSTB]. unfold RDONE.
      do 16 eexists. exists x23, F2, fc2, m4, A3, cap3, P1v, fd. exists DATA3, junk3, (close_errno r3 errv3).
      split; [reflexivity|]. split; [exact HC3|]. split; [| split; [exact FR3| split; [exact BA4| split; [exact ERR4| exact FRM3]]]].
      split; [exact P4|]. split; [exact FA3|]. split; [exact SO3|]. split; [exact HA3|]. split; [exact BLK3|]. split; [exact CAP3|]. split; [exact LEN3| exact BRR3].
  Qed.
End B4.
End CANSEC1.
