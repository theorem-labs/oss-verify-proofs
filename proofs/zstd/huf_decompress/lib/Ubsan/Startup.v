(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun STRW_tac Startup_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Stdio.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg F_memset F_memcpy Startup_A Startup_B StdioFiles.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Startup () := "C47Corelib4Init9Datatypes2IDC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem7raw_lenC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem7pad_lenC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem>raw_len_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem;struct_sizeC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC5ARocqVerifyHarness?AgentSubmission3Lib7InitMemHbuild_stack_bytes_lengthK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg7u_phdrsC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission3Lib7InitMemAlength_simg_boundI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizec5ARocqVerifyHarness?AgentSubmission5Ubsan7Startup>pimg_len_boundI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission3Lib5Nodes7at_nodeI6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc00C5ARocqVerifyHarness?AgentSubmission3Lib5ITree5enodec5ARocqVerifyHarness?AgentSubmission5Ubsan7Startup8pat_mainC5ARocqVerifyHarness?AgentSubmission3Lib5ITree5epostC5ARocqVerifyHarness?AgentSubmission3Lib9RegsEquiv7init_msC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8wrap_memI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem9init_noneC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem8init_stkC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem=init_mem_inv'C5ARocqVerifyHarness?AgentSubmission3Lib7InitMem@init_stack_bytesC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem7init_wrC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem;init_piecesC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem4argcC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib7InitMem9argv_ptrsC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem9envp_ptrsC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem4envcC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem:auxv_wordsC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem8str_baseC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?flatten_stringsC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem8env_baseC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem8rnd_addrC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem9rnd_bytesC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib7InitMem@init_argv_stringC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List<nth_error_InC47Corelib4Init5Logic5proj1C45stdpp9bitvector;definitions5bv_eqC46Stdlib5Lists4List<In_nth_errorC46Stdlib5Lists4List9nth_errorC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?envp_ptr_boundsC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem;draw_canaryC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem;draw_secretC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?rnd_bytes_splitC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_appK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C46Stdlib9micromega;ZifyClasses6eq_iffK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit:libc_cellsC5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit8td_cellsC47Corelib5Lists7ListDef6repeatC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcI4ELinuxProcessSemantics5Riscv7Prelude4tree00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC56Stdlib6ZArith6BinInt1Z4landK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem=bytes_at_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4C56Stdlib6ZArith6BinInt1Z7sub_0_rC5ARocqVerifyHarness?AgentSubmission6Common6StrFun?land_align_downC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission3Lib7SysStep=swrap32_smallC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneI47Corelib4Init5Logic2or00C46Stdlib5Lists4List:length_appC47Corelib4Init3Nat3mulK46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64s_lengthK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast=munch_write_nC47Corelib5Lists7ListDef6firstnK4ELinuxProcessSemantics5Riscv3Sem4core01C47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem@argv_ptrs_lengthC46Stdlib5Lists4List>nth_error_app1C5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit9rd_u64s_gC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit9envp_addrC5ARocqVerifyHarness?AgentSubmission3Lib3Arr8u64s_appC46Stdlib5Lists4List9app_nil_rC5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B7pauxv20C5ARocqVerifyHarness?AgentSubmission3Lib7InitMem@envp_ptrs_lengthC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib7SysStep=stk_lo_nonnegC56Stdlib6ZArith6BinInt1Z4of_NC5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B?rinit_libc_postC5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B?rinit_libc_specC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B9canary_ofC5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit9rtd_cellsK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenK4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releaseK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1K4ELinuxProcessSemantics5Riscv5Instr5instr07C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission3Lib5Frame?wr_at_transportC5ARocqVerifyHarness?AgentSubmission5Ubsan:StdioFiles:file_cellsC5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit<rw_cells_appC5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit9auxv_addrC5ARocqVerifyHarness?AgentSubmission5Ubsan:StdioFiles;stdout_fileC5ARocqVerifyHarness?AgentSubmission5Ubsan:StdioFiles;stderr_fileC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9so_activeC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio6so_bufC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio8so_firstC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9so_lbf_nlC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio8to_bytesC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_17C5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit>impl_epost_evtC5ARocqVerifyHarness?AgentSubmission3Lib7SysStep=impl_from_evtC5ARocqVerifyHarness?AgentSubmission3Lib5ITree4implK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula07K45stdpp9bitvector;definitions2bv01C46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem:rw_bytes_bC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?rw_cells_image0C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?rw_cells_recastC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC47Corelib5Lists7ListDef5skipnC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFastFbytes_at_write_other_nC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast@rw_cells_frame_nC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast;stk_write_nC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsC4ELinuxProcessSemantics5Riscv3Sem2w0I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K4ELinuxProcessSemantics5Riscv5Instr5msize04C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulI47Corelib4Init5Logic5False00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltI47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litc5ARocqVerifyHarness?AgentSubmission5Ubsan7Startup9psp_factsK5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node07C5ARocqVerifyHarness?AgentSubmission3Lib6Decode;dec_set_tidc5ARocqVerifyHarness?AgentSubmission5Ubsan7Startup7pcanaryC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg9u_init_pcI46Stdlib5Lists4List6Exists00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5msize03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C5ARocqVerifyHarness?AgentSubmission4Spec5Stdio;stdout_initc5ARocqVerifyHarness?AgentSubmission5Ubsan7Startup<pcrt_written".
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation rsegs := UImg.usegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AtMain.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (c : word).
  (* [comment removed for export] *)
  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Definition pcrt_written : list (Z * Z) :=
    [(0x2b750, 0x2b751); (0x3b7d0, 0x3b7d8); (0x3b7d8, 0x3b928); (0x5b8b0, 0x5b8e0); (0x5bb10, 0x5bb18); (0x5bb20, 0x5bba0)]%Z.

  Definition pat_main : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x213e4) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x3b8a0)
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x12da0) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 0x12da0) (Z_to_bv 32 0) None m' (seg_rom rsegs)
    /\ mem_inv rsegs m'
    /\ stk rsegs m' (usp0 - 8388608) (usp0 + -48)
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x3b7d8 [C8 (Z_to_bv 64 0x3b7d8); C8 (Z_to_bv 64 0x3b7d8); C8 (Z_to_bv 64 0x3b7d8); C8 z64; C4 (Z_to_bv 64 t)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x3b7fc [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x3b800 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x3b850);
                                 CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x5bb68); CB 24 (repeat (Z_to_bv 8 0) 24); C8 c;
                                 C8 (Z_to_bv 64 0x3b8b0); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x5bb30 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x5bb38 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
                                 C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x5b8a8 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x5bb18 [C8 z64]
    /\ rw_cells rsegs m' 0x5bb20 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells rsegs m' 0x5bb98 [C8 hw]
    /\ rw_cells rsegs m' 0x3b7d0 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells rsegs m' 0x2b748 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells rsegs m' 0x5bb10 [C8 c]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x2a4b0 [C8 z64]
    /\ rw_cells rsegs m' 0x2a4b8 [C8 (Z_to_bv 64 0x12da0); C8 (Z_to_bv 64 0x210c4); C8 (Z_to_bv 64 0x218dc); C8 z64]
    /\ rw_cells rsegs m' 0x2a4d8 [C8 (Z_to_bv 64 0x21810); C8 z64]
    /\ rw_cells rsegs m' 0x2a4e8 [C8 (Z_to_bv 64 0x2a498)]
    /\ rw_cells rsegs m' 0x2a500 [C8 (Z_to_bv 64 0x3b7d0); C8 (Z_to_bv 64 0x5bb28); C8 (Z_to_bv 64 0x5bb20)]
    /\ rw_cells rsegs m' 0x2a518 [C8 (Z_to_bv 64 0x2a490); C8 (Z_to_bv 64 0x2a488)]
    /\ rw_cells rsegs m' 0x2a528 [C8 (Z_to_bv 64 0x5bb10)]
    /\ rw_cells rsegs m' 0x2a530 [C8 (Z_to_bv 64 0x2a498); C8 (Z_to_bv 64 0x2a490)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x2a488 [C8 (Z_to_bv 64 0x12c9c)]
    /\ rw_cells rsegs m' 0x2a490 [C8 (Z_to_bv 64 0x12d10)]
    /\ rw_cells rsegs m' 0x2a498 [C8 (Z_to_bv 64 0x2b568)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x2b750 [C1 (Z_to_bv 8 1)]
    /\ rw_cells rsegs m' 0x2b798 [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' 0x5bb08 [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x2b740 [C8 (Z_to_bv 64 0x2b658)]
    /\ rw_cells rsegs m' 0x2b650 [C8 (Z_to_bv 64 0x2b568)]
    /\ rw_cells rsegs m' 0x5bf50 [C8 z64]
    /\ rw_cells rsegs m' 0x5bf60 [C8 z64]
    /\ stdout_file m' stdout_init
    /\ stderr_file m'
    (* [comment removed for export] *)
    /\ bytes_at rsegs m' usp0 (build_stack_bytes u_phdrs sp0 argv envp uid hw draw)
    /\ wr_at rsegs m' usp0 (Z.of_nat (length (build_stack_bytes u_phdrs sp0 argv envp uid hw draw)))
    /\ nth_error (argv_ptrs sp0 argv envp) 0 = Some (Z_to_bv 64 P0)
    (* [comment removed for export] *)
    /\ (forall a : word, (0x2a000 <= bv_unsigned a < 0x5d000)%Z -> outside pcrt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z.
End AtMain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac pimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

(* [comment removed for export] *)
Ltac pimg_chunk' NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length outside] in Ha |- *; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section Proof.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Notation ph := u_phdrs.
  Notation usp0 := (bv_unsigned sp0).
  Notation img := (build_stack_bytes u_phdrs sp0 argv envp uid hw draw).
  Notation simg := (entry_stack_image u_phdrs sp0 argv envp uid hw draw).

  Lemma pimg_len_bound : (Z.of_nat (length img) <= 2500000)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["Proof"] "h01Hh11ah22_Hh34__p1h44__p2h54__p3h64__p4h74__p5h84__x1h94__x2h:4__x3h;4__x4h<4__x5h=1eh>1vh?2A1h@2A2hA2E1hB2E2hC7__arithhD4__ffhE8__varmaphF5__withG4cstrhH5cstr0hI1zp;2p;1p;3p;4p;7p;6p;8p-1p10000p5p710p9g000LR0p4p70g001<R1p4p710p8p1001]p4p710p1002:p4p710p8p1002Vp4p7210g003BR2p4p710R3p8p1003`p4p710P3p8g004;j2sTg0053j2rTg005kj25Tg006Hj13Tg006mj14Tg007Kj17Tg0080j21Tg008Lj1WTg008jj1VTg009Mj1ITg009mj2ETg00:Mj1FTg00:mR3j20Tg00;Hj1OTP1j3ATg00<Dj2gTg00<jj3aTg00=Aj1`Tg00=Zj1^Tg00>^j3GTg00?8j2\Tg00?lj2ZTg00@Cj2YTg00ABj2XTg00B>j2MTg00BZj1LTg00C?j1=Tg00C^j2:Tg00DGj2UTg00E0j3KTg00EYj3DTg00FBj2TTg00Fnj1STg00GNj3RTg00Gnj2JTg00HLj1QTg00Hjj4HTg00IHj1qTg00Ifj1pTg00JQj2CTg00K4j4PTg00K_j1oTg00LAj3hTg00Ldj2fTg00MFj2eTg00M`j2bTg00NLj3cTg00Nkj4dTg00O]j2NTg00P:j7_Tg00Q@j7iTP2j6jTg00RIj6kTg00Rmj2lTg00SPj7]Tg00T4j7mTg00TXj3nTg00U;j8[Tf0R2#7#7p=6%32#3p=2g00U_R1/12p=9f1R4g00V=R5g00V\R6P6g00W<R7P2Ekp=>g00W\R8/l2p=8P4P5P6P6P7P2g00X:F]p=<f2R9P5P6P6P7P4P2Fmp=?P8P4g00XZP2CPp=BAn842p=;f3R:P5P6P6P7P9P4P2G[p=@P8p,4argvR5p,4envpR;'s1r5;R<'5g00YAR=#3R>#3R?#3R@#3RA#4RB'5RC%6?#3#2#7#2#7#3#6#3#7#3#2#2#4RD,12XI8p,5VARGV%4=%W@RE#VRF#IRG/E5RH#FRI'1RJ%2A#2RA#2RK#4RL,1I'0RM%O5RN%3K#2#2#2RK#2#2#4RO'1RP1EF2#F%7=RQ#7#6#6#6#6#6#6#6#4'1RRX1G=AG51gE1=aF2#`REX1G=AG5g00YfRS%^2g00ZFRT3Gg00Zf,\2=GST'0X101ZG55A0'0'0R0'0RT'0P3PMPT11CDRCP2P3PPP0PCP2p,5VENVP1EG;RU#FRV%4ARA'1RW%O;RX%4KRK'1RYPRX=G=AG;PEX=G=AG;'0RG'0RE'0P3PWPEPCP2P3PYPGPCP21Y5;1X5;#9%9NR3%9XRR%9<RZ%4@R@,M<'0'0'0'0%LH%9I%LU%9Vp-0RUg00[gRHg00\SR[#=R\#=R]#=R^#=R_#=,:81:8_1U8@R_1:8^5K81:8]1:8\9K8_1:8[5D85D85D85D85D8g00]2'T%SH3R%IHP8P8f4RH,J8P9%Q8R[CHP4P8f5R_,J8P:P[CHCH%q8%p8R[f7R\,>[f8R],>[f9R^,>[f:,>[P8%7>R`,C8Rag00]^%8@RbCP,<[5?[5?[5?[5?[%o6R6P[1C8?R?%8K'B,<[P6P[1C8>R>%8A'B,<[P6P[1C8QRQ%8O'B,<[P6P[f;,>[1C8=R=%8L'B,<[5?[P61;=>9h8b%6`#3#2#4R`#8';/;Q/;?/;a%8B';%8D'B,<[C@C@C@C@C@1f[7P2P9g00^ER[,eS1b29=GS[dAc814CdbDbEbFX88X98X:8X;8X<8X3UX4UX5UX6UW7f6R11MH@,0],0\'0,0_11HK11:A11_Of=11HL'015_1,N@/5`/5\/5]/5^/5B/1D[[[[[^88^98^:8^;8^<8^3U^4U^5U^6U^7UP2PJPZPRP315IV,N@/5`#9P<PXPNPVPIP:P_P^f>fBO?bCbHbGPCeb0X2GXBYP4P2O2n2001000000121000000X0EXAWP4P2O2n2001000000121000000b>X20X@PP4P2O2n2001000000121000000X0TX?MP4P2O2n2001000000121000000b>g00^eR2p,3sp0R4P5P;p,3uidRMp,2hwRTp,4drawRPF_,EF#FP2P4P5P;PMPTPPFiEjo"). Qed.

  Lemma psp_facts : (stack_max_size <= usp0)%Z /\ (usp0 + Z.of_nat (length simg) <= 2^64)%Z /\
                    (usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["Proof"] "h02H0h12Hah24__p1h36__sat4h44__x1h54__x2h64__x3h74__x4h81Hh92H1h:2H2h;1Lh<1Mh=7__arithh>4__ffh?6__sat2h@6__sat3hA8__varmaphB5__withC4cstrhD5cstr0hE1vp;1p;2p;7p;6p;4p;3p;<p;Bp;8g006Hj12Tg008Lj1LTg00_\j2^Tg0080R0j23Tg006mj17Tg00`Fj2kTg00:mR1j24Tg008jj1`Tg00`fj7]Tg009mj2HTg00:MR2j1GTg005kR3j2BTg00adj2yTg007Kj1<Tg00P:j7jTg00bAj7hTg00cCR4j2OTg00C?j11Tg00c]j2aTg00MFj2=Tg00d4j6\Tg00d]j4[Tg00BZj1ITg00eDj2ZTg00B>j2PTg00elj3YTg00fPj2XTg00gAj2WTg00C^j2?Tg00EYj3FTg00FBj2zTg00Fnj1xTg00GNj3wTg009Mj1vTg00Gnj2UTg00HLj1rTg00Hjj4KTg00IHj1qTg00Ifj1pTg00Rmj2STg00JQj2@Tg00K_j1oTg00RIj6nTg00TXj3NTg00K4j4MTg00LAj3RTg00gbj3lTg00Ldj2gTg00M`j2mTg00>^j3QTg00NLj3fTg00Nkj4eTg00O]j2TTg00hEl<dTg00hjlBsTg00SPj7VTg00U;j8tTg00T4j7uTf0R5#2#2p=Cg00W\R6g00U_R77Q5p=E%<5#<p=6%25#2#2#2p=A%25#2#2#2#2#2#2#2p=;%15#1p=D%15#1#1#1#1#1#1#1p=c%15#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=b%15#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00iPR8P6P4P2P0g00iof5R0f4R4f3R9f2R:f1R;P5M<dp=JP8P8P8P6P6P6g00jQP2P2P2P3g00k1P0P4P9P:P;P5MBsp=_1375p=5P:g00V=R3g00V\R2P2g00W<R8P6P;g00XZP5CMg00X:R<FVp=81S65p=:P9P3P2P2P8P:P;P5Gtp=9P:P3P2P2P8P;P5Fup=>P;P3P2P2P8P5P<FVp=ip,3VSPg00kTg00YAR<#2R=#2R>#2R?#2R@#CRA#LRBp,3sp0RC'^RD'3REg00lO,3DRF%7@R@,kDRG#ERH'4RI'4P1PEPIg00mJ/3D%L?#`RJg00^eRKPCp,4argvRLp,4envpRMp,3uidRNp,2hwROp,4drawRPF]'HRQ#GRR,BD%7=RS%7ART'yRU'3%<<RV#6#6#6#6#6RW#6#6#2#C#A#;#;#;#7RX/3D%AARA#2#A#;#;#;#;#7RY,3D'4,4H'4'4RZP5P1PFPHPZP5g00nGPKPCPLPMPNPOPPFj,HJRJ#GR1%6>#2#C#<#C#<#2#6#2#<#2#A#7R['3PKPCPLPMPNPOPPFh1OJQRPg00\SRO#DRN#DRM#1RL#D#c#b#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0RC,aJRK,OQR\'4R]P]131RR]%7WRW,B1R^,3RR_'4R`PPP\P]P_PJP11=61R_PQPR1=6RR\EJPQPRP\PKP^PJP1P_PCPW1=6WE_EJE\P5C[P`%IJ%51%IQ%5R1ZST1P7SRQ%5T1P7U[RJ[%5SR`g00oHRCAYST;UW1%5U\C^1`1XD@%5D%5@R`%5G[[P:g00od1W7S'=PQeO1PJp-0RJg00[gRQ1?6L1?6M1?6N1?6O5F65F65F6g00]2'z%xQ3w%vQP6P61U64P:%r6CKP;1U69CK%q6%p6R9P91S67RQ1@6<R<589%o2ROP9%:@989QPO1@6VRV989QC9C9POP9P9P3P2P2P8f6R2En1@6=R=1@6>R>%:W5N65895>9POP9%:[989>POP9P6PVg010JPQCM,i9RQPOP9%:Y989<RVPOP9%:X=89<R>PO%7?R?#:%7ARA#:RO5R6=R6O=89<AN6<=%:S=l6B589A>9>V9>9Q5>95>9C9C9C9C9C9C91g98P5P:g00YfR9g00^ER8'=1m5:=Q98dAf67;Ceb>bAbBX46X56X66X76W2%55%54\`[1B4W,3:,40130[%E0134Y13X01T?A/TA/32f7RA,B2/3Uf8#E13X2132Y'4'4'4'4[[[[[[^46^56^66^76^2JP5P]P1PGPRPDP:PAf9f:f;f?O;b=b3b?b@b3bDbCb:b9b0PZeX<HX8FP;P5O2n2001000010121000000X0IX;EP;P5O2n2001000010121000000bEo"). Qed.

  (* [comment removed for export] *)
  Definition pcanary : word := canary_of (Z_to_bv 64 (draw_canary draw)).

  Theorem pstartup_spec :
    impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost (fun _ => pat_main sp0 argv envp uid hw draw pcanary))
         (init_ms rsegs u_init_pc u_phdrs sp0 argv envp uid hw draw).
  Proof.
    destruct psp_facts as (SPLO & IMGHI & SP16 & SPW).
    pose proof pimg_len_bound as IL. pose proof (length_simg_bound u_phdrs sp0 argv envp uid hw draw) as ILS.
    unfold init_ms, mkR_init. change (Z.of_N u_init_pc) with 0x12c54%Z.
    set (m := wrap_mem ph sp0 argv envp uid hw draw).
    assert (NONE : forall a : word, (bv_unsigned a < 0x5d000)%Z -> m a = None).
    { intros a Ha. apply init_none. unfold stack_max_size. lia. }
    pose proof (init_stk rsegs ph sp0 argv envp uid hw draw SPLO) as ST. fold m in ST.
    change stack_max_size with 8388608%Z in ST.
    pose proof (init_mem_inv' rsegs ph sp0 argv envp uid hw draw SPLO IMGHI ltac:(change (segs_top rsegs) with 0x5d000%Z; unfold stack_max_size; lia)) as MI.
    fold m in MI.
    pose proof (init_stack_bytes rsegs ph sp0 argv envp uid hw draw SPLO IMGHI) as IMG. fold m in IMG.
    pose proof (init_wr rsegs ph sp0 argv envp uid hw draw SPLO IMGHI) as WR. fold m in WR. rewrite <- (build_stack_bytes_length ph sp0 argv envp uid hw draw) in WR.
    destruct (init_pieces rsegs ph sp0 argv envp uid hw draw SPLO IMGHI) as (ARGC & ARGV & ENVP & AUXW & _ & _ & RNDB). fold m in ARGC, ARGV, ENVP, AUXW, RNDB.
    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct argv as [|a ?]; [cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (init_argv_string rsegs ph sp0 argv envp uid hw draw SPLO IMGHI 0 arg0 Harg0) as (P0 & HP0 & P0LO & P0HI & STR).
    fold m in STR.
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    assert (EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs sp0 argv envp)).
    { apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [i Hi].
      pose proof (envp_ptr_bounds ph sp0 argv envp uid hw draw IMGHI i w Hi).
      pose proof (raw_len_nonneg argv envp). unfold env_base, str_base, struct_size in *. lia. }
    assert (RND : bytes_at rsegs m (rnd_addr sp0 argv envp) (le8 (Z_to_bv 64 (draw_canary draw)))).
    { rewrite rnd_bytes_split in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
    assert (RLO : (usp0 <= rnd_addr sp0 argv envp)%Z).
    { pose proof (raw_len_nonneg argv envp). unfold rnd_addr, raw_len. lia. }
    pimg_chunk NONE m 0x5bb20%Z [C8 z64; C8 z64] G2.
    pimg_chunk NONE m 0x5bb98%Z [C8 z64] HW.
    pimg_chunk NONE m 0x3b7d0%Z [C8 z64] ENVC.
    pimg_chunk NONE m 0x5bb18%Z [C8 z64] SI.
    pimg_chunk NONE m 0x5bb30%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    pimg_chunk NONE m 0x3b7d8%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    pimg_chunk NONE m 0x5b8a8%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    pimg_chunk NONE m 0x2b748%Z [C4 (Z_to_bv 64 0x20000)] DS.
    pimg_chunk NONE m 0x5bb10%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    pimg_chunk NONE m 0x2a500%Z [C8 (Z_to_bv 64 0x3b7d0); C8 (Z_to_bv 64 0x5bb28); C8 (Z_to_bv 64 0x5bb20)] GOT3.
    pimg_chunk NONE m 0x2a528%Z [C8 (Z_to_bv 64 0x5bb10)] GG.
    pimg_chunk NONE m 0x2a4b0%Z [C8 z64] GD.
    pimg_chunk NONE m 0x2a4b8%Z [C8 (Z_to_bv 64 0x12da0); C8 (Z_to_bv 64 0x210c4); C8 (Z_to_bv 64 0x218dc); C8 z64] GOT0.
    pimg_chunk NONE m 0x2a518%Z [C8 (Z_to_bv 64 0x2a490); C8 (Z_to_bv 64 0x2a488)] GIN.
    pimg_chunk NONE m 0x2a488%Z [C8 (Z_to_bv 64 0x12c9c)] INA.
    pimg_chunk NONE m 0x2b750%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 184 <= P0)%Z).
    { pose proof (raw_len_nonneg argv envp). unfold str_base, struct_size in P0LO. lia. }
    pose proof (munch_refl [(usp0 - 8388608, usp0); (0x2b750, 0x2b751); (0x3b7d0, 0x3b7d8); (0x3b7d8, 0x3b928);
                            (0x5b8b0, 0x5b8e0); (0x5bb10, 0x5bb18); (0x5bb20, 0x5bba0)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    clearbody m.
    change (id (bytes_at rsegs m usp0 img)) in IMG. change (id (wr_at rsegs m usp0 (Z.of_nat (length img)))) in WR.
    iprefix.
    do 7 lstep.
    pose proof (bytes_at_read rsegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0x21340%Z.
    carve_frame 32%nat ST.
    do 8 lstep.
    pose proof (rd_u64s_g rsegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (ENV : bytes_at rsegs m1 (envp_addr sp0 argv)
                    (u64s (envp_ptrs sp0 argv envp) ++ le8 z64 ++ u64s (pauxv20 hw uid (Z_to_bv 64 (rnd_addr sp0 argv envp))))).
    { rewrite u64s_app in ENVP. cbn [u64s] in ENVP. rewrite app_nil_r in ENVP.
      apply bytes_at_app in ENVP. destruct ENVP as [E1 E2]. rewrite u64s_length, envp_ptrs_length in E2.
      unfold envp_addr. apply bytes_at_app. split; [exact E1|]. apply bytes_at_app. split.
      - rewrite u64s_length, envp_ptrs_length. exact E2.
      - rewrite u64s_length, envp_ptrs_length, length_le8.
        replace (usp0 + 8 * (argc argv + 2) + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z
          with (usp0 + 8 * (argc argv + envc envp + 3))%Z by lia.
        exact AUXW. }
    clear ENVP AUXW ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    icallk (rinit_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 8388608)%Z
              (envp_addr sp0 argv) (envp_ptrs sp0 argv envp) (rnd_addr sp0 argv envp) P0 arg0 _ _ _ _ uid hw (Z_to_bv 64 (draw_canary draw))).
    all: lazymatch goal with
         | |- forall _, _ => ipost rsegs; unname_sp
         | |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | unfold envp_addr; lia ]
         end.
    rename PC into ST.
    unfold td_cells, rtd_cells, libc_cells, envp_addr in *.
    repeat match goal with
           | H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
           | H : bytes_at _ _ P0 _ |- _ => clear H
           | H : bytes_at _ _ (rnd_addr _ _ _) _ |- _ => clear H
           end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 P0HI RLO.
    steps_to 0x2139c%Z. release_frame FR ST (bv_unsigned sp0). astep.
    carve_frame 48%nat ST. steps_to 0x212f4%Z.
    carve_frame 32%nat ST. steps_to 0x12c9c%Z.
    carve_frame 16%nat ST. steps_to 0x12d0c%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x2133c%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
    steps_to 0x12da0%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport rsegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport rsegs m mf) in WR; [| exact WM] end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0x5d000)%Z ->
                outside [(usp0 - 8388608, usp0); (0x2b750, 0x2b751); (0x3b7d0, 0x3b7d8); (0x3b7d8, 0x3b928);
                         (0x5b8b0, 0x5b8e0); (0x5bb10, 0x5bb18); (0x5bb20, 0x5bba0)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      pimg_chunk' NONE' mf 0x2a4d8%Z [C8 (Z_to_bv 64 0x21810); C8 z64] GCX;
      pimg_chunk' NONE' mf 0x2a4e8%Z [C8 (Z_to_bv 64 0x2a498)] GSE;
      pimg_chunk' NONE' mf 0x2a530%Z [C8 (Z_to_bv 64 0x2a498); C8 (Z_to_bv 64 0x2a490)] GFI;
      pimg_chunk' NONE' mf 0x2a490%Z [C8 (Z_to_bv 64 0x12d10)] FIA;
      pimg_chunk' NONE' mf 0x2a498%Z [C8 (Z_to_bv 64 0x2b568)] SEP;
      pimg_chunk' NONE' mf 0x2b798%Z [C1 (Z_to_bv 8 0)] FIN;
      pimg_chunk' NONE' mf 0x5bb08%Z [C4 z64] EXL;
      pimg_chunk' NONE' mf 0x2b740%Z [C8 (Z_to_bv 64 0x2b658)] SOU;
      pimg_chunk' NONE' mf 0x2b650%Z [C8 (Z_to_bv 64 0x2b568)] SEU;
      pimg_chunk' NONE' mf 0x5bf50%Z [C8 z64] SIN;
      pimg_chunk' NONE' mf 0x5bf60%Z [C8 z64] OFL;
      pimg_chunk' NONE' mf 0x2b658%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x2404c 0x5bf78 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      pimg_chunk' NONE' mf 0x5bf78%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      pimg_chunk' NONE' mf 0x2b568%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x23eb4 0x5bf70 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.
    lazymatch goal with TD : rw_cells _ _ 0x3b7d8 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0x3b7fc%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0x3b800%Z in TDb by reflexivity end.
    lazymatch goal with L : rw_cells _ _ 0x5bb30 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0x5bb38%Z in LCb by reflexivity end.
    apply evt_done. unfold pat_main, envp_addr.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
         | |- stdout_file _ _ =>
             exists (Z_to_bv 64 5), z64, (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024);
             cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length to_bytes map firstn];
             split; [exact SOF|]; split; [reflexivity|]; split; [exact SBUF|]; split; [reflexivity|];
             split; [apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity|]; intros _; reflexivity
         | |- stderr_file _ => exists (Z_to_bv 64 5), z64, 0%Z, 0%Z, (repeat (Z_to_bv 8 0) 80); exact SEF
         | |- nth_error _ _ = _ => exact HP0
         | |- wr_at _ _ _ _ => exact WR
         | |- forall _, _ => intros a Ha Hout; rewrite (MU a); [apply NONE; lia|];
                              unfold pcrt_written in Hout; cbn [outside] in Hout |- *; lia
         | |- _ => first [hyp_by_addr | lia]
         end.
  Qed.
End Proof.
