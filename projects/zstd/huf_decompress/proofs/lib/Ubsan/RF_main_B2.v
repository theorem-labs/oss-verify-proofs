(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (rw_cells_CB0, rw_cells_CB_join, rd_read_core and 1 more); rd_read_core, rd_read restated for the revision's model; the zero-mapped stack depth; rd_read_core and rd_read are zstd/simple_decompress's proofs, with this binary's addresses). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg F_syscalls F_memcpy StdioFiles Startup Exit F_printf_iface Stdio_iface Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_main_B2 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List8map_consK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib3Mem<bytes_at_nilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib6Common:Stdio_pure<rw_cells_appC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC47Corelib4Init5Logic5proj2C47Corelib4Init3Nat3addC47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;Stdio_iface@fwrite_diag_postC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree8impl_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface@emit_printf_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver5rd_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_main_B1<fprintf_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem9argv_ptrsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib5Ubsan:RF_main_B15STAGEC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib5Ubsan;RDriver_ctx6MFRAMEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RF_main_A4BASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctx8sp_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctx2LOC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib5Ubsan=RMalloc_iface5RHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver9rd_result00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00C59OSSVerify5KrLib5Ubsan:RF_main_B18POSTBODYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface<rblock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctx5RSTATC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC59OSSVerify5KrLib5Ubsan=RDriver_iface;trun_cells0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Harness_iface<stderr_file0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3sum02C59OSSVerify5KrLib4Spec6Driver<u8s_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib3Lib3Tac7sum_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3TacArw_cells_split_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5Ubsan:F_syscalls9read_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:F_syscalls9read_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_kit>implM_of_enodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:F_syscalls8read_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib5Lists7ListDef5skipnI47Corelib4Init5Peano2le00I47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Startup_kit9envp_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem4argcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib5Ubsan9RF_main_A3WOKC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib5Ubsan9RF_main_A<RHEAP_munchWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RF_main_A:BASE_munchC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan8F_atexit9atx_stateC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib5Ubsan;RDriver_kit<argv_cstringC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem8str_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RF_main_A8IMGB_lenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr05C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib3Lib7ZBridge=bv_lts_zero_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree@map_unsigned_posC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5Ubsan9RF_main_A8IMGB_topC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib6Common8DrvAgreeDzbytes_map_unsigned'C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5Ubsan>F_printf_iface9diag_argsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_iface8pat_exitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtK59OSSVerify5KrLib3Lib6Decode8read_ans01C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<length_skipnC59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib3Lib7SysStepArw_cells_bytes_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9Stdio_kit<memcpy_postvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9Stdio_kit<memcpy_callvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init9Datatypes3sum01C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat7eqb_neqc59OSSVerify5KrLib5Ubsan:RF_main_B2@rw_cells_CB_joinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_main_B13BUFC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_main_B15RDINVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib5Ubsan:RF_main_B15RDBRKC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode8read_ans02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:rd_contentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6rd_capC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6rd_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_main_B1<rd_read_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles;stdout_fileC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver5rd_st01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep6RERRNOC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9MAX_INPUTC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode8read_ans00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg;UREAD_STAGEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C59OSSVerify5KrLib5Ubsan7RunDraw:PSTAGE_LENC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv3Sem4core00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib5Ubsan:RMallocRep4RATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan7RunDraw<PSTAGE_LEN_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg7u_phdrsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec4Prog2ioC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_iface5PMAINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_iface;PSTAGE2_RETC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathK4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC59OSSVerify5KrLib6Common;Printf_fmts@A_FMT_read_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles;GLOBALS_TOPC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C47Corelib7Program6Basics4implI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C47Corelib7Classes?RelationClasses>impl_ReflexiveC59OSSVerify5KrLib3Lib8PropExec5v_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_subC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C59OSSVerify5KrLib3Lib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5b_luiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_gec59OSSVerify5KrLib5Ubsan:RF_main_B2<rd_read_coreC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ua := idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT} {lx : launchT}.
Lemma rw_cells_CB0 : forall m A, 0 <= A <= 2^64 -> rw_cells usegs m A [CB 0%nat []].
Proof.
  intros m A H. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes app]. apply bytes_at_nil. exact H.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma rw_cells_CB_join : forall m A n1 n2 (b1 b2 : list byte),
  rw_cells usegs m A [CB n1 b1] -> rw_cells usegs m (A + Z.of_nat n1) [CB n2 b2] ->
  rw_cells usegs m A [CB (n1 + n2)%nat (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 H1 H2.
  assert (H : rw_cells usegs m A ([CB n1 b1] ++ [CB n2 b2])).
  { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H2. }
  destruct H as [[Hwf HB] HW]. cbn in Hwf. destruct Hwf as (L1 & L2 & _).
  split; [split|].
  - cbn. rewrite length_app. split; [lia| exact I].
  - cbn [cells_bytes cbytes app] in HB |- *. rewrite !app_nil_r in HB |- *. exact HB.
  - replace (Z.of_nat (cells_size [CB (n1 + n2)%nat (b1 ++ b2)])) with (Z.of_nat (cells_size ([CB n1 b1] ++ [CB n2 b2]))) by (cbn; lia). exact HW.
Qed.

Section B2.
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
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 UREAD_STAGE) x23 t3 t4 t5 t6 F fc mm).

  (* [comment removed for export] *)
  Lemma rd_read_core : forall (fd P1v : Z) (st1 : rd_st) (s : PState) x1 t0 t1 t2 a1 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A CNT : Z) (DATA junk sj : list byte) (errv : word),
    3 <= fd < 2^32 -> nth_error (argv_ptrs L_TOP argv envp L_EXECFN) 1 = Some (Z_to_bv 64 P1v) ->
    rd_content st1 = map bv_unsigned DATA -> BUF mm s (rd_buf st1) A (rd_cap st1) DATA junk -> STAGE mm sj ->
    Z.of_nat (length DATA) < rd_cap st1 ->
    CNT = (if 65536 <? rd_cap st1 - Z.of_nat (length DATA) then 65536 else rd_cap st1 - Z.of_nat (length DATA)) ->
    FRAME' mm -> BASE' mm -> rw_cells usegs mm RERRNO [C4 errv] -> frm0 fc ->
    implM usegs (rd_read_part fd (map bv_unsigned arg1) st1) s (POSTBODY' fd P1v)
      (GST 0x12e7c x1 t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 65536) a1 (Z_to_bv 64 CNT) a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (Z.of_nat (length DATA))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 UREAD_STAGE) x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros FD HP1 HC BU SJ LT ECNT0 FR BA ERR FRM.
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
    destruct BU as (P0 & FA0 & SO0 & _ & BLK & [CAPR CAPK] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts. pose proof PSTAGE_LEN_Z as PSTAGER.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST.
    assert (LENZ : zlength (rd_content st1) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    unfold MAX_INPUT in CAPR.
    assert (CNTR : 1 <= CNT <= 65536 /\ CNT <= rd_cap st1 - Z.of_nat (length DATA)).
    { rewrite ECNT0. destruct (Z.ltb_spec0 65536 (rd_cap st1 - Z.of_nat (length DATA))); lia. }
    unfold rd_read_part. cbv zeta. rewrite LENZ, <- ECNT0.
    unfold MFRAME in FR. unfold RERRNO in ERR. unfold STAGE, UREAD_STAGE in SJ.
    unfold implM. iprefix.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs _ _ [] _ _ [] [Z.to_nat CNT; (PSTAGE_LEN - Z.to_nat CNT)%nat]) in SJ; [| cbn; lia].
    cbn [mk_CB_cells app] in SJ.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in SJ. destruct SJ as [SJ1 SJ2]. cbn [cells_size csize Nat.add] in SJ2.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
    set (LEN := Z.of_nat (length DATA)) in *.
    assert (ELEN : LEN = Z.of_nat (length DATA)) by reflexivity. clearbody LEN. assert (LEN0 : 0 <= LEN) by lia.
    eapply implM_bind.
    { set (w1 := Z_to_bv 64 UREAD_STAGE). unfold UREAD_STAGE in w1.
      replace UREAD_STAGE with (bv_unsigned w1) by (subst w1; unfold UREAD_STAGE; rewrite unsigned_lit; lia).
      eapply implM_of_enode.
      eapply read_spec with (lo := usp0 - 6144513) (junk := firstn (Z.to_nat CNT) sj) (errv := errv); subst w1; unfold RATP;
        rewrite ?(unsigned_lit 243872) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit 178073) by lia; try reflexivity;
        first [exact ST | exact SJ1 | exact ERR | exact MI | lia]. }
    cbv beta. intros a s' ms' [PO ->].
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & RES).
    unfold RATP in MUc, RES. rewrite !unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in RES by lia.
    change (243872 + -164) with 243708 in MUc, RES.
    transport_after_call usegs mm m2 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x12e88)) with (Z_to_bv 64 0x12e88) by (symmetry; rpc).
    rename ST2 into ST2'.
    assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 16, usp0 + -128); (178073, 178073 + Z.of_nat (Z.to_nat CNT)); (243708, 243708 + 4)]).
    { unfold WOK, LO, RERRNO, UREAD_STAGE. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    assert (P2 : RHEAP s [(rd_buf st1, A, rd_cap st1)] m2).
    { eapply (RHEAP_munchW sp0 argv envp VSP); [exact WOKW| exact MUc| exact WMc| | exact P0].
      intros iv [<-|[<-|[<-|[]]]]; cbn [fst snd]; intros Hiv Hiv2; exfalso; lia. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid hw draw TID VSP VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; first [exact ST2' | replace (usp0 - 6144513) with (usp0 + -6144513) by lia; exact ST2']]).
    (* [comment removed for export] *)
    remember (firstn (PSTAGE_LEN - Z.to_nat CNT) (skipn (Z.to_nat CNT) sj)) as JR eqn:EJR. clear EJR.
    clear MUc WMc BA WOKW.
    destruct a as [e|bs]; cbn [read_ret] in *.
    - (* [comment removed for export] *)
      destruct RES as (SJ1' & ERR2 & He).
      pose proof BA2 as (ST3 & MI3 & RS3 & AUX3 & IMG3 & SE3 & SOF3 & TR3). pose proof RS3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _).
      pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).
      destruct (argv_cstring sp0 argv envp uid hw draw m2 IMG3 (dvalid_padok _ _ _ VSP) 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
        as (p1 & slack1 & HP1' & P1LO & P1HI & STR1 & SLK1).
      pose proof (layout_bounds L_LA sp0 L_TOP argv envp L_EXECFN (dvalid_padok _ _ _ VSP)) as (LBS & _).
      pose proof (Nat2Z.is_nonneg (block_head_size (la_rseq L_LA) argv envp)). unfold hsz in LBS.
      pose proof (IMGB_len sp0 argv envp uid hw draw VSP VARGV VENVP) as IL.
      rewrite HP1 in HP1'. assert (EP : Z_to_bv 64 P1v = Z_to_bv 64 p1) by congruence. rewrite EP. clear HP1' EP.
      assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
      assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
      unfold implM. iprefix.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
      cbn [io_diag Prog.io io_S].
      eapply (fprintf_exit sp0 argv envp uid hw draw TID S8 S9 S10 S11 VSP HT FPR FWX SWF (DReadError (map bv_unsigned arg1)));
        [| exact BA2| exact P2| exact SO0| exact FRM| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
      unfold F_fmt_fp_lib.zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
      split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
      split; [unfold FmtFp.INT_MAX; lia|]. split; [right; lia|]. split; [unfold GLOBALS_TOP; lia|].
      pose proof (IMGB_top sp0 argv envp uid hw draw VSP). lia.
    - destruct RES as (SJ1' & ERR2 & Hbs).
      pose proof (bytes_at_bound _ _ _ _ (proj2 (proj1 SJ1'))) as BB. cbn [cells_bytes cbytes app] in BB. rewrite !length_app, length_skipn in BB.
      unfold implM. iprefix.
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0 Hbs CAPR LEN0 CNTR LENR; clear; intros; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        pose proof BA2 as (ST3 & MI3 & RS3 & AUX3 & IMG3 & SE3 & SOF3 & TR3). unfold LO in ST3.
        (* [comment removed for export] *)
        apply (proj1 (rw_cells_app _ _ _ [CB (length bs) bs] _)) in SJ1'. destruct SJ1' as [SJa SJb]. cbn [cells_size csize Nat.add] in SJb.
        pose proof (rw_cells_bytes_at _ _ _ _ SJa) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB.
        (* [comment removed for export] *)
        pose proof BLK as BLK2. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLK2. destruct BLK2 as [BLK1 BLK2].
        cbn [cells_size csize Nat.add] in BLK2. replace (length DATA + 0)%nat with (length DATA) in BLK2 by lia.
        apply (rw_cells_split_CB usegs _ _ [] _ _ [] [length bs; (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat]) in BLK2; [| cbn; lia].
        cbn [mk_CB_cells app] in BLK2.
        apply (proj1 (rw_cells_app _ _ _ [_] _)) in BLK2. destruct BLK2 as [BLK2 BLK3]. cbn [cells_size csize Nat.add] in BLK3.
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { eapply memcpy_callv with (src := bs) (junk := firstn (length bs) junk);
            [ unfold UREAD_STAGE; exact SRCB | lia | replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) by lia; replace (A + LEN) with (A + Z.of_nat (length DATA)) by lia; exact BLK2
            | unfold UREAD_STAGE; lia | lia | unfold UREAD_STAGE; lia | lia | exact MI3 ]. }
        cbv beta. intros ms'' PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MUd & WMd & MI4 & NB & _).
        ua. transport_after_call usegs m2 m3 MUd WMd.
        replace (ret_pc (Z_to_bv 64 0x12e20)) with (Z_to_bv 64 0x12e20) by (symmetry; rpc).
        assert (WOKD : Forall (WOK sp0) [(A + LEN, A + LEN + Z.of_nat (length bs))]).
        { unfold WOK. constructor; [right; right; left; cbn [fst snd]; lia| constructor]. }
        assert (P3 : RHEAP s [(rd_buf st1, A, rd_cap st1)] m3).
        { eapply (RHEAP_munchW sp0 argv envp VSP); [exact WOKD| exact MUd| exact WMd| | exact P2].
          intros iv [<-|[]]. cbn [fst snd]. intros _ _. exists (rd_buf st1, A, rd_cap st1). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
        assert (BA3 : BASE' m3) by (eapply (BASE_munch sp0 argv envp uid hw draw TID VSP VARGV VENVP); [exact BA2| exact WOKD| exact MUd| exact WMd| exact MI4| unfold LO; first [exact ST3 | replace (usp0 - 6144513) with (usp0 + -6144513) by lia; exact ST3]]).
        clear MUd WMd WOKD.
        zstep. zstep.
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
        replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; intros E; rewrite E in K1; apply K1; reflexivity).
        apply implM_ret. apply evt_done. cbn [POSTBODY]. unfold RDINV. cbn [rd_content rd_cap rd_buf].
        assert (LEN' : zlength (rd_content st1 ++ u8s_of_bytes bs) = LEN + Z.of_nat (length bs)).
        { unfold zlength, u8s_of_bytes. rewrite length_app, length_map. unfold zlength in LENZ. lia. }
        rewrite LEN'.
        (* [comment removed for export] *)
        pose proof (rw_cells_CB_join _ _ _ _ _ _ BLK1 ltac:(replace (A + Z.of_nat (length DATA)) with (A + LEN) by lia; replace (length bs) with (Z.to_nat (Z.of_nat (length bs))) by lia; exact NB)) as BLK1'.
        replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) in BLK1' by lia.
        assert (BLK' : rw_cells usegs m3 A [CB (length (DATA ++ bs)) (DATA ++ bs); CB (Z.to_nat (rd_cap st1 - Z.of_nat (length (DATA ++ bs)))) (firstn (Z.to_nat (rd_cap st1 - LEN) - length bs) (skipn (length bs) junk))]).
        { apply (proj2 (rw_cells_app _ _ _ [CB (length (DATA ++ bs)) (DATA ++ bs)] _)). rewrite length_app. split; [exact BLK1'|]. cbn [cells_size csize Nat.add].
          replace (A + Z.of_nat (length DATA + length bs + 0)) with (A + Z.of_nat (length DATA) + Z.of_nat (length bs + 0)) by lia.
          replace (Z.to_nat (rd_cap st1 - Z.of_nat (length DATA + length bs))) with (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat by lia. exact BLK3. }
        (* [comment removed for export] *)
        pose proof (rw_cells_CB_join _ _ _ _ _ _ SJb ltac:(replace (178073 + Z.of_nat (length bs + 0) + Z.of_nat (Z.to_nat CNT - length bs)) with (178073 + Z.of_nat (Z.to_nat CNT + 0)) by lia; exact SJ2)) as SJc.
        pose proof (rw_cells_CB_join _ _ _ _ _ _ SJa ltac:(replace (178073 + Z.of_nat (length bs)) with (178073 + Z.of_nat (length bs + 0)) by lia; exact SJc)) as SJ'.
        do 17 eexists. exists F, fc, m3, A, (DATA ++ bs), (firstn (Z.to_nat (rd_cap st1 - LEN) - length bs) (skipn (length bs) junk)), (Z_to_bv 64 (bv_unsigned errv)).
        exists (bs ++ (skipn (length bs) (firstn (Z.to_nat CNT) sj) ++ JR)), 0x12e28.
        split; [replace (Z.of_nat (length bs) + LEN) with (LEN + Z.of_nat (length bs)) by lia; reflexivity|].
        split; [left; split; reflexivity|].
        split; [rewrite HC; unfold u8s_of_bytes; rewrite map_app; reflexivity|].
        split; [| split; [| split; [exact FR| split; [exact BA3| split; [| exact FRM]]]]].
        3:{ replace (Z_to_bv 64 (bv_unsigned errv)) with errv by (symmetry; apply Z_to_bv_bv_unsigned). exact ERR2. }
        { split; [exact P3|]. split; [exact FA0|]. split; [exact SO0|]. split; [exact I|]. split; [exact BLK'|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [rewrite length_app; lia| exact BR]. }
        { unfold STAGE, UREAD_STAGE. replace PSTAGE_LEN with (length bs + (Z.to_nat CNT - length bs + (PSTAGE_LEN - Z.to_nat CNT)))%nat at 1 by lia. exact SJ'. }
      + (* [comment removed for export] *)
        assert (Ebs : bs = []) by (destruct bs; [reflexivity| cbn [length] in K1; exfalso; rewrite ?unsigned_lit in K1 by lia; lia]). subst bs.
        cbn [length Nat.eqb]. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
        apply implM_ret. apply evt_done.
        cbn [POSTBODY]. unfold RDBRK.
        do 17 eexists. exists F, fc, m2, A, (rd_cap st1), DATA, junk, (Z_to_bv 64 (bv_unsigned errv)).
        split; [rewrite LENZ; cbn [Z.of_nat]; reflexivity|].
        split; [exact HC|]. split; [| split; [exact FR| split; [exact BA2| split; [| exact FRM]]]].
        2:{ replace (Z_to_bv 64 (bv_unsigned errv)) with errv by (symmetry; apply Z_to_bv_bv_unsigned). exact ERR2. }
        split; [exact P2|]. split; [exact FA0|]. split; [exact SO0|]. split; [exact I|]. split; [rewrite <- ELEN; exact BLK|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [lia| exact BR].
  Qed.

  (* [comment removed for export] *)
Lemma rd_read : forall (fd P1v : Z) (st1 : rd_st) (s : PState) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z) (DATA junk sj : list byte) (errv : word),
3 <= fd < 2^32 -> nth_error (argv_ptrs L_TOP argv envp L_EXECFN) 1 = Some (Z_to_bv 64 P1v) ->
rd_content st1 = map bv_unsigned DATA -> BUF mm s (rd_buf st1) A (rd_cap st1) DATA junk -> STAGE mm sj ->
Z.of_nat (length DATA) < rd_cap st1 ->
FRAME' mm -> BASE' mm -> rw_cells usegs mm RERRNO [C4 errv] -> frm0 fc ->
implM usegs (rd_read_part fd (map bv_unsigned arg1) st1) s (POSTBODY' fd P1v)
(GST 0x12e6c x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (zlength (rd_content st1))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 UREAD_STAGE) x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros FD HP1 HC BU SJ LT FR BA ERR FRM.
    pose proof BU as (_ & _ & _ & _ & _ & [CAPR CAPK] & LENR & _). unfold MAX_INPUT in CAPR.
    pose proof BA as (_ & MI & _).
    assert (LENZ : zlength (rd_content st1) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    rewrite LENZ.
    unfold implM. eapply impl_evt; [| intros ms' H; exact H].
    zstep. zstep. zstep. if_cases KW; zify_cond KW.
    - (* [comment removed for export] *)
      apply evt_done.
      replace (Z_to_bv 64 (rd_cap st1 + - Z.of_nat (length DATA))) with (Z_to_bv 64 (rd_cap st1 - Z.of_nat (length DATA))) by (f_equal; lia).
      eapply (rd_read_core fd P1v st1 s); try eassumption.
      replace (65536 <? rd_cap st1 - Z.of_nat (length DATA)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - (* [comment removed for export] *)
      zstep. apply evt_done.
      eapply (rd_read_core fd P1v st1 s); try eassumption.
      destruct (Z.ltb_spec0 65536 (rd_cap st1 - Z.of_nat (length DATA))); [reflexivity| lia].
  Qed.
End B2.
End CANSEC1.
