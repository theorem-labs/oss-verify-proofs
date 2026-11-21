(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (5 recorded proofs replaced by written proofs (shiftr26_zero_iff, rd_nogrow, rd_grow and 2 more); rd_nogrow, rd_grow, rd_body and 1 more restated for the revision's model; the zero-mapped stack depth; rd_nogrow, rd_grow, rd_body, rd_loop are zstd/simple_decompress's proofs, with this binary's addresses). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem MonadX.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg F_syscalls F_memcpy StdioFiles Startup Exit F_printf_iface Stdio_iface Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_main_B3 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z;div_le_monoK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z8div_sameK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic9False_indK46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z9div_smallK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver7IOStyle00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver>read_loop_bodyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;Stdio_iface@fwrite_diag_postC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree8impl_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface@emit_printf_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver5rd_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_main_B1?implM_mret_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_unrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad<implM_loop_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_main_B1<fprintf_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_main_B1;fwrite_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI46Stdlib5Lists4List5NoDup00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib7InitMem9argv_ptrsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitions;bv_unsignedC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib4Spec6Driver6rd_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_main_B13BUFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_main_B15STAGEC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5Ubsan;RDriver_ctx6MFRAMEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RF_main_A4BASEC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctx2LOC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctx5RSTATC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Harness_iface<stderr_file0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles;stdout_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_iface;trun_cells0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver9rd_result00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00C59OSSVerify5KrLib5Ubsan:RF_main_B1<rd_read_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_main_B18POSTBODYC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib5Ubsan:RF_main_B27rd_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:rd_contentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6rd_capC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5Ubsan:RMallocRep6RERRNOC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg7u_phdrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep4RATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg;UREAD_STAGEC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib3Lib6MonadX@implM_bind_assocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctx8sp_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface<rblock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_diagC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbK59OSSVerify5KrLib4Spec6Driver8diag_msg03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3sum02C56Stdlib5Arith8PeanoNat3Nat3eqbK59OSSVerify5KrLib4Spec6Driver9rd_result02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver<u8s_of_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK47Corelib4Init9Datatypes3sum01K4ELinuxProcessSemantics5Riscv5Instr5instr09C59OSSVerify5KrLib3Lib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC59OSSVerify5KrLib3Lib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge9zr_shiftrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqc59OSSVerify5KrLib5Ubsan:RF_main_B3Ashiftr26_zero_iffC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic6eq_symK59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan8F_atexit9atx_stateC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C59OSSVerify5KrLib3Lib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5b_luiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface9diag_argsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_iface8pat_exitC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib3Lib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib6Malloc8ProgDeps:raw_mallocC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing3Pol01C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib5Ubsan=RMalloc_iface<rmalloc_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface5RHEAPC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface=raddr_exposedC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5Ubsan=RMalloc_iface:rheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RF_main_A>BASE_heap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Startup_kit9envp_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem4argcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib5Ubsan=RMalloc_ifaceCrheap_pres_rw_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib5Ubsan>RMalloc_ifacePHRHEAP_blocks_nodup_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RMalloc_ifacePKRHEAP_blocks_disjoint_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks6blk_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_iface9dvalid_spC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC59OSSVerify5KrLib6Malloc8ProgDeps8raw_freeC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC59OSSVerify5KrLib3Lib3Tac7sum_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3TacArw_cells_split_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib6Common:Stdio_pure<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStepArw_cells_bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib5Ubsan9Stdio_kit<memcpy_postvC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9Stdio_kit<memcpy_callvC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib5Ubsan9RF_main_A3WOKC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC59OSSVerify5KrLib5Ubsan9RF_main_A<RHEAP_munchWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RF_main_A:BASE_munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface:rfree_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_facts5mleafC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_facts<implM_leavesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<Malloc_iface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_facts@lb_remove_secondC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC56Stdlib6ZArith6BinInt1ZApow_lt_mono_r_iffC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC59OSSVerify5KrLib3Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B3:after_testC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver5rd_st01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib6Malloc8ProgDeps8ptr_addrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9MAX_INPUTC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode8read_ans00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib5Ubsan:RMallocRep5RLIBCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib5Ubsan7RunDraw:PSTAGE_LENC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC59OSSVerify5KrLib5Ubsan7RunDraw<PSTAGE_LEN_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog2ioC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg04C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC59OSSVerify5KrLib6Common;Printf_fmts=A_FMT_too_bigC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03C59OSSVerify5KrLib5Ubsan=RMalloc_iface=RMALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_iface5PMAINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_iface;PSTAGE2_RETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C59OSSVerify5KrLib5Ubsan=RMalloc_iface;RFREE_STACKC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C47Corelib7Classes?RelationClasses>impl_ReflexiveC59OSSVerify5KrLib5Ubsan:RF_main_B15RDINVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_main_B1<rd_grow_partC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B37rd_growC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B39rd_nogrowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib5Ubsan:RF_main_B1Aread_loop_body_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B38POSTLOOPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B37rd_bodyC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_ind".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ua := idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT} {lx : launchT}.
Lemma shiftr26_zero_iff : forall a, 0 <= a -> (Z.shiftr a 26 = 0 <-> a < 67108864).
Proof.
  intros a Ha. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 26) with 67108864.
  split; intros H; [| apply Z.div_small; lia].
  destruct (Z.lt_ge_cases a 67108864) as [L|G]; [exact L|]. exfalso.
  pose proof (Z.div_le_mono 67108864 a 67108864 ltac:(lia) G) as M. rewrite Z.div_same in M by lia. lia.
Qed.

Section B3.
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
  Notation IMGB := (build_stack_bytes L_LA pph (Z_to_bv 64 (Z.of_N u_init_pc)) sp0 L_TOP argv envp L_EXECFN uid L_GID hw draw).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw draw TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm J8 S7 S6 S5 S4).
  Notation RDINV' := (RDINV sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).
  Notation RDBRK' := (RDBRK sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).
  Notation POSTBODY' := (POSTBODY sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).
  Ltac hyps := first [exact VSP | exact VARGV | exact VENVP | exact EARGV | exact HT | exact MALLOC | exact FREE | exact FPR | exact FWX | exact SWF | exact FWR | exact TOW].

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition after_test (fd : Z) (st : rd_st) : M PState (rd_st + rd_result) :=
    g <- (if MAX_INPUT <=? rd_cap st then io_diag Prog.io DTooBig ;;; mret None
          else nb <- raw_malloc (rd_cap st * 2) ;;
               match nb with
               | None => io_diag Prog.io DOom ;;; mret None
               | Some nb' => raw_free (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
               end) ;;
    match g with None => mret (inr RdExit) | Some st1 =>
         let want0 := rd_cap st1 - zlength (rd_content st) in
         let cnt := if 65536 <? want0 then 65536 else want0 in
         a <- msys (NRead fd UREAD_STAGE cnt) (dec_read UREAD_STAGE cnt) ;;
         match a with
         | RdErr _ => io_diag Prog.io (DReadError (map bv_unsigned arg1)) ;;; mret (inr RdExit)
         | RdData bs =>
             if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
             else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
         end end.

  (* [comment removed for export] *)
Lemma rd_nogrow : forall (fd P1v : Z) (st : rd_st) (s : PState) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z) (DATA junk sj : list byte) (errv : word),
3 <= fd < 2^32 -> nth_error (argv_ptrs L_TOP argv envp L_EXECFN) 1 = Some (Z_to_bv 64 P1v) ->
rd_content st = map bv_unsigned DATA -> BUF mm s (rd_buf st) A (rd_cap st) DATA junk -> STAGE mm sj ->
Z.of_nat (length DATA) < rd_cap st ->
FRAME' mm -> BASE' mm -> rw_cells usegs mm RERRNO [C4 errv] -> frm0 fc ->
implM usegs (rd_read_part fd (map bv_unsigned arg1) st) s (POSTBODY' fd P1v)
(GST 0x12e2c x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (zlength (rd_content st))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st)) (Z_to_bv 64 UREAD_STAGE) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros FD HP1 HC BU SJ LT FR BA ERR FRM.
    pose proof BA as (_ & MI & _).
    unfold implM. eapply impl_evt; [| intros ms' H; exact H].
    zstep. zstep. apply evt_done.
    eapply (rd_read sp0 argv envp uid hw draw arg0 arg1 TID J8 S4 S5 S6 S7 S8 S9 S10 S11);
      first [hyps | exact FD | exact HP1 | exact HC | exact BU | exact SJ | exact BA | exact FR | exact ERR | exact FRM | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rd_grow : forall (fd P1v : Z) (st : rd_st) (s : PState) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z) (DATA junk sj : list byte) (errv : word),
    3 <= fd < 2^32 -> nth_error (argv_ptrs L_TOP argv envp L_EXECFN) 1 = Some (Z_to_bv 64 P1v) ->
    rd_content st = map bv_unsigned DATA -> BUF mm s (rd_buf st) A (rd_cap st) DATA junk -> STAGE mm sj ->
    Z.of_nat (length DATA) = rd_cap st ->
    FRAME' mm -> BASE' mm -> rw_cells usegs mm RERRNO [C4 errv] -> frm0 fc ->
    implM usegs (after_test fd st) s (POSTBODY' fd P1v)
      (GST 0x12e34 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (zlength (rd_content st))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st)) (Z_to_bv 64 UREAD_STAGE) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros FD HP1 HC BU SJ K00 FR BA ERR FRM.
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
    assert (LENZ : zlength (rd_content st) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BU as (P0 & FA0 & SO0 & _ & BLK & [CAPR [k [K0' CAPK]]] & LENR & BR). unfold MAX_INPUT in CAPR.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts. pose proof PSTAGE_LEN_Z as PSTAGER.
    unfold STAGE, UREAD_STAGE in SJ.
    rewrite LENZ. unfold after_test.
    unfold implM. iprefix.
    zstep. zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (GE : 67108864 <= rd_cap st).
      { destruct (Z.lt_ge_cases (rd_cap st) 67108864) as [L|G]; [| exact G]. exfalso. apply K0.
        apply (proj2 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). lia. }
      replace (MAX_INPUT <=? rd_cap st) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia).
      pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _).
      zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
      apply implM_bind_assoc. cbn [io_diag io_S].
      eapply (fprintf_exit sp0 argv envp uid hw draw TID S8 S9 S10 S11 VSP HT FPR FWX SWF DTooBig);
        [| exact BA| exact P0| exact SO0| exact FRM| intros ms'' AE; apply implM_mret_bind; cbv beta iota; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args]. split; [reflexivity|]. rewrite unsigned_lit by lia. reflexivity. }
    (* [comment removed for export] *)
    assert (LTM : rd_cap st < 67108864).
    { rewrite <- K00. apply (proj1 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). exact K0. }
    replace (MAX_INPUT <=? rd_cap st) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
    zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
    apply implM_bind_assoc.
    replace (Z.shiftl (Z.of_nat (length DATA)) 1) with (rd_cap st * 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    eapply implM_bind.
    { unfold rmalloc_stmt in MALLOC.
      eapply MALLOC with (lo := usp0 - 6144513) (B := usp0); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 243872) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        first [ exact P0 | exact AUX | exact ST | exact ERR | exact MI | unfold RMALLOC_STACK; lia | lia ]. }
    cbv beta. intros r s1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & FAE & SOE & RR).
    unfold RATP in ERR1. rewrite ?(unsigned_lit 243872) in ERR1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
    change (243872 + -164) with 243708 in ERR1.
    replace (ret_pc (Z_to_bv 64 0x12e48)) with (Z_to_bv 64 0x12e48) by (symmetry; rpc).
    assert (BA1 : BASE' m1) by (eapply (BASE_heap_pres sp0 argv envp uid hw draw TID); [exact BA| exact HPR| exact MI1| unfold LO; first [exact ST1| replace (usp0 - 6144513) with (usp0 + -6144513) by lia; exact ST1]| exact AUX1]).
    assert (FR1 : FRAME' m1) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]). unfold MFRAME in FR1.
    assert (BLK1 : rw_cells usegs m1 A [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st - Z.of_nat (length DATA))) junk]).
    { eapply rheap_pres_rw_cells; [exact HPR| exact BLK|]. right; right. exists (rd_buf st, A, rd_cap st). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
    assert (SJ1 : rw_cells usegs m1 178073 [CB PSTAGE_LEN sj]).
    { eapply rheap_pres_rw_cells; [exact HPR| exact SJ|]. right; left. cbn [cells_size csize Nat.add]. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
    clear FR BLK SJ ST MI AUX IMG RS SE SOF ERR.
    destruct r as [nb|].
    2:{ (* [comment removed for export] *)
        destruct RR as [-> HEAP1].
        pose proof BA1 as (ST & MI & RS & AUX & IMG & SE & SOF & TR1). unfold LO in ST.
        pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _).
        unfold implM. iprefix. zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 (POSTBODY' fd P1v) msx) end.
        apply implM_bind_assoc. cbn [io_diag io_S].
        eapply (fwrite_exit sp0 argv envp uid hw draw TID S8 S9 S10 S11 VSP HT FWR TOW);
          [exact BA1| exact HEAP1| rewrite SOE; exact SO0| intros ms'' AE; apply implM_mret_bind; cbv beta iota; apply implM_ret; apply evt_done; exact AE]. }
    (* [comment removed for export] *)
    destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & HEXP).
    pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HEAP1) as ND.
    assert (DISJ : A' + rd_cap st * 2 <= A \/ A + rd_cap st <= A').
    { pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (nb, A', rd_cap st * 2) (rd_buf st, A, rd_cap st) HEAP1 ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
      cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst. intros E. apply NI. rewrite E. left. reflexivity. }
    apply implM_bind_assoc.
    pose proof BA1 as (ST & MI & RS & AUX & IMG & SE & SOF & TR1). unfold LO in ST.
    unfold implM. iprefix. zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
    zstep. zstep. if_cases K2; zify_cond K2; try (exfalso; lia). clear K2.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB _ _ _ [] _ _ [] [length DATA; Z.to_nat (rd_cap st * 2) - length DATA]%nat) in NBLK; [| cbn; lia]. cbn [mk_CB_cells app] in NBLK.
    apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) (firstn (length DATA) junk')] _)) in NBLK. destruct NBLK as [NB1 NB2]. cbn [cells_size csize Nat.add] in NB2.
    pose proof BLK1 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in SRC. destruct SRC as [SRC _].
    pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
    eapply evt_cut.
    { eapply memcpy_callv with (src := DATA) (junk := firstn (length DATA) junk');
        [exact SRCB| lia| replace (Z.to_nat (Z.of_nat (length DATA))) with (length DATA) by lia; exact NB1| lia| lia| lia| lia| exact MI]. }
    cbv beta. intros ms' PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & NB1' & _).
    ua. transport_after_call usegs m1 m2 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x12e64)) with (Z_to_bv 64 0x12e64) by (symmetry; rpc).
    assert (WOKW : Forall (WOK sp0) [(A', A' + Z.of_nat (length DATA))]).
    { unfold WOK. constructor; [right; right; left; cbn [fst snd]; lia| constructor]. }
    assert (P2 : RHEAP s1 [(nb, A', rd_cap st * 2); (rd_buf st, A, rd_cap st)] m2).
    { eapply (RHEAP_munchW sp0 argv envp VSP); [exact WOKW| exact MUc| exact WMc| | exact HEAP1].
      intros iv [<-|[]]. cbn [fst snd]. intros _ _. exists (nb, A', rd_cap st * 2). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid hw draw TID VSP VARGV VENVP); [exact BA1| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; first [exact ST| replace (usp0 - 6144513) with (usp0 + -6144513) by lia; exact ST]]).
    clear MUc WMc BA1 ST MI RS AUX IMG SE SOF WOKW TR1.
    pose proof BA2 as (ST & MI & RS & AUX & IMG & SE & SOF & TR2). unfold LO in ST.
    (* [comment removed for export] *)
    zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 (POSTBODY' fd P1v) msx) end.
    eapply implM_bind.
    { apply implM_leaves. unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 6144513) (B := usp0) (p := rd_buf st) (A := A) (n := rd_cap st); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit 243872) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        first [ exact P2 | right; left; reflexivity | exact AUX | exact ST | exact MI | exact ERR1 | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 [PO LEAF].
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    unfold RATP in ERR3. rewrite ?(unsigned_lit 243872) in ERR3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    change (243872 + -164) with 243708 in ERR3.
    replace (ret_pc (Z_to_bv 64 0x12e6c)) with (Z_to_bv 64 0x12e6c) by (symmetry; rpc).
    rewrite (lb_remove_second (rd_buf st) (nb, A', rd_cap st * 2) (rd_buf st, A, rd_cap st) [] eq_refl ND) in HPR3, HEAP3.
    assert (BA3 : BASE' m3) by (eapply (BASE_heap_pres sp0 argv envp uid hw draw TID); [exact BA2| exact HPR3| exact MI3| unfold LO; first [exact ST3| replace (usp0 - 6144513) with (usp0 + -6144513) by lia; exact ST3]| exact AUX3]).
    assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR3| exact FR1| left; cbn; lia]).
    assert (NB3 : rw_cells usegs m3 A' [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) (firstn (Z.to_nat (rd_cap st * 2) - length DATA)%nat (skipn (length DATA) junk'))]).
    { eapply rheap_pres_rw_cells; [exact HPR3| |].
      - apply (proj2 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)). split; [replace (length DATA) with (Z.to_nat (Z.of_nat (length DATA))) at 1 by lia; exact NB1'|].
        cbn [cells_size csize Nat.add]. replace (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) with (Z.to_nat (rd_cap st * 2) - length DATA)%nat by lia. exact NB2.
      - right; right. exists (nb, A', rd_cap st * 2). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
    assert (SJ3 : rw_cells usegs m3 178073 [CB PSTAGE_LEN sj]).
    { eapply rheap_pres_rw_cells; [exact HPR3| exact SJ1|]. right; left. cbn [cells_size csize Nat.add]. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
    clear HPR3 FR1 NB1' NB2 LEAF.
    apply implM_mret_bind. cbv beta iota.
    rewrite <- LENZ.
    eapply (rd_read sp0 argv envp uid hw draw arg0 arg1 TID J8 S4 S5 S6 S7 S8 S9 S10 S11 VSP VARGV VENVP EARGV HT FPR FWX SWF fd P1v (mkRd nb (rd_cap st * 2) (rd_content st)) s2);
      cbn [rd_buf rd_cap rd_content]; first [exact FD | exact HP1 | exact HC | exact FR3 | exact BA3 | unfold RERRNO; exact ERR3 | exact FRM | lia | idtac].
    - split; [exact HEAP3|]. split; [rewrite FAE3; exact (eq_trans FAE FA0)|]. split; [rewrite SOE3; exact (eq_trans SOE SO0)|]. split; [exact I|]. split; [exact NB3|].
      assert (CAP2 : rd_cap st * 2 <= 67108864).
      { rewrite CAPK in LTM |- *. change 67108864 with (2 ^ 26) in LTM |- *. apply Z.pow_lt_mono_r_iff in LTM; [| lia| lia].
        replace (2 ^ k * 2) with (2 ^ (k + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
      unfold MAX_INPUT. split; [split; [lia| exists (k + 1); split; [lia| rewrite CAPK, Z.pow_add_r by lia; lia]]|]. split; [lia| exact BR'].
    - unfold STAGE, UREAD_STAGE. exact SJ3.
  Qed.

  (* [comment removed for export] *)
Lemma rd_body : forall (fd P1v : Z) (st : rd_st) (s : PState) ms,
3 <= fd < 2^32 -> nth_error (argv_ptrs L_TOP argv envp L_EXECFN) 1 = Some (Z_to_bv 64 P1v) ->
RDINV' fd P1v st s ms ->
implM usegs (read_loop_body Prog.io raw_malloc raw_free UREAD_STAGE fd (map bv_unsigned arg1) st) s (POSTBODY' fd P1v) ms.
  Proof.
    intros fd P1v st s ms FD HP1 RI.
    destruct RI as (x1 & t0 & t1 & t2 & x9 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & A & DATA & junk & errv & sj & pc
                    & -> & PCX & HC & BU & SJ & FR & BA & ERR & FRM).
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
    assert (LENZ : zlength (rd_content st) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BU as (P0 & FA0 & SO0 & _ & BLK & [CAPR [k [K0' CAPK]]] & LENR & BR). unfold MAX_INPUT in CAPR.
    pose proof BA as (ST & MI & _). unfold LO in ST.
    rewrite read_loop_body_eq. unfold rd_grow_part. rewrite LENZ.
    unfold implM. iprefix.
    destruct PCX as [[-> ->]|[-> HNIL]].
    - (* [comment removed for export] *)
      zstep. if_cases K00; zify_cond K00.
      + (* [comment removed for export] *)
        replace (Z.of_nat (length DATA) =? rd_cap st) with true by (symmetry; apply Z.eqb_eq; lia).
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
        rewrite <- LENZ. eapply (rd_grow fd P1v st s); rewrite ?LENZ; first [exact FD | exact HP1 | exact HC | exact BU | exact SJ | exact FR | exact BA | exact ERR | exact FRM | lia].
      + (* [comment removed for export] *)
        replace (Z.of_nat (length DATA) =? rd_cap st) with false by (symmetry; apply Z.eqb_neq; lia).
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
        apply implM_mret_bind. cbv iota beta.
        rewrite <- LENZ. eapply (rd_nogrow fd P1v st s); first [exact FD | exact HP1 | exact HC | exact BU | exact SJ | exact FR | exact BA | exact ERR | exact FRM | lia].
    - (* [comment removed for export] *)
      assert (D0 : DATA = []) by (destruct DATA; [reflexivity| rewrite HNIL in HC; discriminate]). subst DATA. cbn [length Z.of_nat] in *.
      zstep. if_cases K00; zify_cond K00; [| exfalso; rewrite ?unsigned_lit in K00 by lia; lia].
      replace (0 =? rd_cap st) with false by (symmetry; apply Z.eqb_neq; lia).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
      apply implM_mret_bind. cbv iota beta.
      rewrite <- LENZ. eapply (rd_nogrow fd P1v st s); first [exact FD | exact HP1 | exact HC | exact BU | exact SJ | exact FR | exact BA | exact ERR | exact FRM | cbn [length Z.of_nat]; lia].
  Qed.

  (* [comment removed for export] *)
  Definition POSTLOOP (fd P1v : Z) (r : rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | RdExit => pat_exit 2 s ms
    | RdDone b c => RDBRK' fd P1v b c s ms
    end.

Lemma rd_loop : forall (fuel : nat) (fd P1v : Z) (st : rd_st) (s : PState) ms,
3 <= fd < 2^32 -> nth_error (argv_ptrs L_TOP argv envp L_EXECFN) 1 = Some (Z_to_bv 64 P1v) ->
RDINV' fd P1v st s ms ->
implM usegs (mloop fuel (read_loop_body Prog.io raw_malloc raw_free UREAD_STAGE fd (map bv_unsigned arg1)) st) s (POSTLOOP fd P1v) ms.
  Proof.
    induction fuel as [|fuel IH]; intros fd P1v st s ms FD HP1 RI.
    - cbn [mloop]. apply implM_unr.
    - apply implM_loop_S. eapply implM_mono; [apply rd_body; [exact FD| exact HP1| exact RI]|].
      intros [st'|[|b c]] s' ms' PO; cbn [POSTBODY POSTLOOP] in PO |- *.
      + apply IH; [exact FD| exact HP1| exact PO].
      + apply evt_done. exact PO.
      + apply evt_done. exact PO.
  Qed.
End B3.
End CANSEC1.
