(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of zal_ex, dest_length, gfa_t367e4, gfa_loop, gfa_tail_spec, gfa_head and 1 more replaced by plain proofs). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Arr Walk SysStep ITree.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import R_small R_m2s R_thread R_cache_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import R_prim_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
Ltac2 kr_t_R_getfrom () := "C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00c69OSSVerify5KrLib2K53B239R_getfrom4destC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib2K53Lib3Mem4sx32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr3updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr:upd_lengthC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subK69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B239R_getfrom:gfa_tail_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs5SB_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B239R_getfrom;dest_lengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7comparec69OSSVerify5KrLib2K53B239R_getfrom6zal_exC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K56Common8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast6sf_ad1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_addr_ztobvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast7sf_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C69OSSVerify5KrLib2K53Lib8StepFast8sf_congTC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC69OSSVerify5KrLib2K53Lib8StepFast@sf_store8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_install_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib2K53Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphC69OSSVerify5KrLib2K53Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr04K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C69OSSVerify5KrLib2K53Lib3Arr<u32arr_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC69OSSVerify5KrLib2K56Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib2K53Lib8StepFast6sf_ad4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast?sf_load8_directC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC69OSSVerify5KrLib2K56Common8PropExec5v_luiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC69OSSVerify5KrLib2K56Common8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C69OSSVerify5KrLib2K56Common8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C69OSSVerify5KrLib2K56Common8PropExec6v_slliC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC4ELinuxProcessSemantics5Riscv7Prelude4zextC69OSSVerify5KrLib2K56Common8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Image>ro_cells_imageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib2FP9bv_lit_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@ro_cells_read_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast<sf_load_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C69OSSVerify5KrLib2K53Lib8StepFast7sf_btgtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_cong1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_andC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C69OSSVerify5KrLib2K56Common8PropExec7alu_andC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib2K53Lib8StepFast<sf_branch_pcC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib2K56Common8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zC69OSSVerify5KrLib2K53Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec6v_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC69OSSVerify5KrLib2K56Common8PropExec8alu_srliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C56Stdlib6ZArith6BinInt1Z4landC69OSSVerify5KrLib2K53Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib2K53Lib7ZBridge9zr_land_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge?zb_shl_shr_landC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr0DK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC69OSSVerify5KrLib2K53Lib6MState:interp_effC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics5Riscv3Sem3eff06C4ELinuxProcessSemantics5Riscv3Sem5is_x0K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff07C69OSSVerify5KrLib2K53Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4tgetC69OSSVerify5KrLib2K53Lib6MState8step_genC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K4ELinuxProcessSemantics5Riscv5Instr5instr0EK4ELinuxProcessSemantics5Riscv3Sem3eff08C35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib2K53Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC4ELinuxProcessSemantics5Riscv7Prelude4tsetC4ELinuxProcessSemantics5Riscv3Sem7reg_getC69OSSVerify5KrLib2K53Lib8StepFast6sf_ad2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C69OSSVerify5KrLib2K53B23;R_prim_defs7ri_lockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs7ri_tailC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B239R_getfrom<gfa_ret_postC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B239R_getfrom5gfa_QC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C69OSSVerify5KrLib2K53Lib8StepFast?sf_install_loadC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib2K56Common8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C69OSSVerify5KrLib2K53Lib8StepFast;sf_evt_stepC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics5Riscv3Sem2w0C69OSSVerify5KrLib2K53Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03C69OSSVerify5KrLib2K53B235R_m2s>kHighShadowEndC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr6awidth02I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums8positive00C4ELinuxProcessSemantics5Riscv3Sem2w1C69OSSVerify5KrLib2K53Lib6MState6w1_litC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib2K53B23;R_prim_defs2faC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z8max_specC69OSSVerify5KrLib2K53B23<R_cache_defs<nth_error_exC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib2K53Lib3Arr;u32arr_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr?u32arr_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C69OSSVerify5KrLib2K53Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_store_goalC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr<u32arr_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=nth_error_nthC56Stdlib6ZArith4Znat5Z2Nat7inj_addc69OSSVerify5KrLib2K53B239R_getfrom:gfa_t367e4C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib2K53Lib8StepFast:sf_evt_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK4ELinuxProcessSemantics5Riscv5Instr5msize03c69OSSVerify5KrLib2K53B239R_getfrom9gfa_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs6fl_arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B239R_getfrom8gfa_loopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C69OSSVerify5KrLib2K53B23;R_prim_defs6RIS_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs5rinfoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs:inst_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC47Corelib5Lists7ListDef6firstnK46Stdlib9micromega5Tauto8GFormula01C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec4v_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC69OSSVerify5KrLib2K56Common8PropExec6alu_orC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC69OSSVerify5KrLib2K53Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cb_split_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cb_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs4INSTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B239R_getfrom9gfa_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs:i_spacebegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs;i_premappedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09C69OSSVerify5KrLib2K53B23;R_prim_defs7ri_coreC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B239R_getfrom=gfa_fast_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr@u32arr_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B239R_getfrom:gfa_fast_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z6ltb_geC69OSSVerify5KrLib2K56Common8PropExec5v_subC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib2K56Common8PropExec7alu_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B239R_getfrom=gfa_tail_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B239R_getfrom8gfa_headC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop02".   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Notation mem := (word -> option byte).

Definition gfa_entry : Z := 0xa6234.

(* [comment removed for export] *)
Definition gfa_frame (m : mem) (sp : word) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  exists junk, rw_cells asegs m (bv_unsigned sp - 128)
    [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Fixpoint dest (ws chs : list word) (base : Z) (i : nat) : list word :=
  match i with
  | O => chs
  | S j => upd (dest ws chs base j) j (sx32 (nth (Z.to_nat base + j) ws (Z_to_bv 64 0)))
  end.

Lemma dest_length : forall ws chs base i, length (dest ws chs base i) = length chs.
Proof. intros ws chs base i. induction i as [|i IH]; cbn [dest]; [reflexivity|]. rewrite upd_length. exact IH. Qed.

(* [comment removed for export] *)
Definition gfa_tail_W (sp : word) (R CH n : Z) : list (Z * Z) :=
  [(R, R + 8); (R + 72, R + 80); (CH, CH + 4 * n); (bv_unsigned sp - 128, bv_unsigned sp)]%Z.

Definition gfa_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R CH n : Z) (chs' : list word) (rand : word) (exh : byte) (pad : list byte) (nalloc nfreed r0 r1 r2 r3 lo : Z)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (gfa_tail_W sp R CH n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ ri_lock m' R 0
    /\ ri_tail m' R rand exh pad (nalloc + n) nfreed r0 r1 r2 r3
    /\ u32arr asegs m' CH chs'
    /\ stk asegs m' lo (bv_unsigned sp).

Section GTAIL.
Variables (ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word) (F : bvmap 5 word) (fc : bv 32).
Variables (ACEIL SB c R CH n nfree' lo : Z) (ws chs : list word) (rand : word) (exh : byte) (pad : list byte)
          (nalloc nfreed r0 r1 r2 r3 : Z) (m0 : mem).
Hypothesis HSB : SB_ok ACEIL SB.
Hypothesis Hc : (1 <= c <= 31)%Z.
Hypothesis ER : R = rinfo (RIS_of SB) c.
Hypothesis Hn : (1 <= n <= 16)%Z.
Hypothesis Hnf : (0 <= nfree')%Z.
Hypothesis Hws : (4 * (nfree' + n) <= 4 * Z.of_nat (length ws) <= 2^29)%Z.
Hypothesis Hchs : length chs = 16%nat.
Hypothesis HCH : (0 < CH /\ CH + 64 <= ACEIL /\ (CH + 64 <= SB \/ SB + 2^37 + 4096 <= CH))%Z.
Hypothesis Hna : (0 <= nalloc < 2^64)%Z.
Hypothesis HLO : (ACEIL <= lo)%Z.
Hypothesis HLOH : (kHighShadowEnd + 8 <= lo)%Z.
Hypothesis HLO2 : (lo <= bv_unsigned sp - 128)%Z.
Hypothesis HSP : (bv_unsigned sp <= 2^47)%Z.

Definition gfa_Q : machine_state -> Prop :=
  gfa_ret_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F fc R CH n (dest ws chs nfree' (Z.to_nat n))
    rand exh pad nalloc nfreed r0 r1 r2 r3 lo m0.

(* [comment removed for export] *)
Lemma gfa_t367e4 : forall ra' t0 t1 t2 s1 a0 a1 a2 a3 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (m : mem) junk,
  rw_cells asegs m (bv_unsigned sp - 128)
    [CB 24 junk; C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
  rw_cells asegs m R [C8 (Z_to_bv 64 1152921504606846976)] ->
  rw_cells asegs m (R + 64) [C4 rand; C1 exh; CB 3 pad; C8 (Z_to_bv 64 nalloc); C8 (Z_to_bv 64 nfreed);
                             C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3)] ->
  u32arr asegs m CH (dest ws chs nfree' (Z.to_nat n)) ->
  stk asegs m lo (bv_unsigned sp - 128) ->
  munch (gfa_tail_W sp R CH n) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  evt asegs gfa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 128)) gp tp t0 t1 t2 (Z_to_bv 64 R) s1 a0 a1 a2 a3 (Z_to_bv 64 n)
             a5 a6 a7 s2 (Z_to_bv 64 2305843009213693952) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa63bc) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros FR LK RT CHS ST MU WM MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  unfold rinfo, RIS_of, kHighShadowEnd, gfa_tail_W in *.
  pose proof (dest_length ws chs nfree' (Z.to_nat n)) as DL.
  zhide.
  do 4 zstep.
  do 14 zstep.
  zstep.
  do 2 zstep. zstep. ifF.
  zstep. zstep. ifT.
  do 7 zstep. zstep. ifT.
  assert (AMO : amo_aligned AD (Z_to_bv 64 R) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. rewrite ER. Z.div_mod_to_equations. lia. }
  amo_step AMO.
  zstep. ifF.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  zstep. ifT.
  zstep. ifT.
  do 15 zstep.
  replace (bv_unsigned sp - 128 + 128)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma gfa_loop : forall (k : nat) (i : Z) ra' t0 t1 t2 s1 a0 a2 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (m : mem) junk,
  i = (n - Z.of_nat k)%Z -> (0 <= i)%Z -> (1 <= k)%nat ->
  rw_cells asegs m (bv_unsigned sp - 128)
    [CB 24 junk; C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
  rw_cells asegs m R [C8 (Z_to_bv 64 1152921504606846976)] ->
  rw_cells asegs m (R + 64) [C4 rand; C1 exh; CB 3 pad; C8 (Z_to_bv 64 nalloc); C8 (Z_to_bv 64 nfreed);
                             C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3)] ->
  u32arr asegs m (fa SB c) ws ->
  u32arr asegs m CH (dest ws chs nfree' (Z.to_nat i)) ->
  stk asegs m lo (bv_unsigned sp - 128) ->
  munch (gfa_tail_W sp R CH n) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  evt asegs gfa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 128)) gp tp t0 t1 t2 (Z_to_bv 64 R) s1 a0 (Z_to_bv 64 (CH + 4 * n)) a2
             (Z_to_bv 64 (CH + 4 * i)) (Z_to_bv 64 n) a5 a6 a7 s2 (Z_to_bv 64 2305843009213693952)
             (Z_to_bv 64 (fa SB c + 4 * (nfree' + i))) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa63a8) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra' t0 t1 t2 s1 a0 a2 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m junk
    Ei Hi Hk FR LK RT FL CHS ST MU WM MI; [lia|].
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  unfold rinfo, RIS_of, kHighShadowEnd, gfa_tail_W in *.
  pose proof (dest_length ws chs nfree' (Z.to_nat i)) as DL.
  assert (FAB : (SB + 2^32 <= fa SB c /\ fa SB c + 2^29 <= SB + 2^37)%Z) by (unfold fa, rb; lia).
  destruct (nth_error_ex ws (Z.to_nat (nfree' + i)) ltac:(lia)) as [w Hw].
  pose proof (u32arr_read asegs m (fa SB c) ws (nfree' + i) w (Z_to_bv 64 (fa SB c + 4 * (nfree' + i))) FL Hw ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zhide.
  zstep. clear RD.
  pose proof (u32arr_store_ok asegs m CH _ i (Z_to_bv 64 (CH + 4 * i)) CHS ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SO.
  zstep.
  pose proof (u32arr_write asegs m CH _ i (sx32 w) CHS ltac:(lia)) as CHS'.
  clear CHS.
  store_done.
  assert (EW : w = nth (Z.to_nat nfree' + Z.to_nat i) ws (Z_to_bv 64 0)).
  { rewrite <- Z2Nat.inj_add by lia. symmetry. apply nth_error_nth. exact Hw. }
  replace (upd (dest ws chs nfree' (Z.to_nat i)) (Z.to_nat i) (sx32 w)) with (dest ws chs nfree' (Z.to_nat (i + 1))) in CHS'
    by (replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; cbn [dest]; rewrite <- EW; reflexivity).
  do 2 zstep.
  replace (CH + 4 * i + 4)%Z with (CH + 4 * (i + 1))%Z by lia.
  replace (fa SB c + 4 * (nfree' + i) + 4)%Z with (fa SB c + 4 * (nfree' + (i + 1)))%Z by lia.
  zstep.
  destruct k as [|k].
  - ifF.
    replace (i + 1)%Z with n in CHS' by lia.
    eapply gfa_t367e4; eassumption.
  - ifT.
    eapply (IH (i + 1)%Z); try eassumption; lia.
Qed.

Lemma gfa_tail_spec : forall ra' t0 t1 t2 s1 a0 a1 a2 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
  gfa_frame m0 sp ra s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o ->
  ri_lock m0 R 1152921504606846976 ->
  ri_tail m0 R rand exh pad nalloc nfreed r0 r1 r2 r3 ->
  fl_arr m0 SB c ws -> u32arr asegs m0 CH chs ->
  stk asegs m0 lo (bv_unsigned sp - 128) ->
  mem_inv asegs m0 ->
  evt asegs gfa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 128)) gp tp t0 t1 t2 (Z_to_bv 64 R) s1 a0 a1 a2 (Z_to_bv 64 CH) (Z_to_bv 64 n)
             (Z_to_bv 64 nfree') a6 a7 s2 (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (fa SB c)) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0xa6398) fc None m0 (seg_rom asegs)).
Proof.
  intros until t6. intros FR LK RT FL CHS ST MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  unfold rinfo, RIS_of, kHighShadowEnd, ri_lock, ri_tail, fl_arr, gfa_frame in *.
  destruct FR as (junk & FR).
  pose proof (munch_refl (gfa_tail_W sp R CH n) m0) as MU. pose proof (wmono_refl asegs m0) as WM. unfold gfa_tail_W in MU.
  pose proof (dest_length ws chs nfree' 0) as DL.
  zhide.
  do 4 zstep.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2)%Z with 4%Z.
  replace (fa SB c + nfree' * 4)%Z with (fa SB c + 4 * (nfree' + 0))%Z by lia.
  replace (CH + n * 4)%Z with (CH + 4 * n)%Z by lia.
  assert (E0 : Z_to_bv 64 CH = Z_to_bv 64 (CH + 4 * 0)) by (f_equal; lia). rewrite E0.
  eapply (gfa_loop (Z.to_nat n) 0%Z); try eassumption; try lia.
Qed.
End GTAIL.

(* [comment removed for export] *)
Lemma gfa_head : forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R stat CH n lo : Z) (Q : machine_state -> Prop),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  inst_cells SB m -> ri_lock m R 0 ->
  stk asegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 128)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  (forall (m1 : mem) (junk : list byte),
     rw_cells asegs m1 (bv_unsigned sp - 128)
       [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     rw_cells asegs m1 R [C8 (Z_to_bv 64 1152921504606846976)] ->
     stk asegs m1 lo (bv_unsigned sp - 128) ->
     munch [(R, R + 8); (bv_unsigned sp - 128, bv_unsigned sp)]%Z m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
     evt asegs Q
       (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 128)) gp tp (Z_to_bv 64 0) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 0)
                (Z_to_bv 64 R) (Z_to_bv 64 INST) (Z_to_bv 64 (R + 8)) (Z_to_bv 64 stat) (Z_to_bv 64 c) (Z_to_bv 64 CH)
                (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s2 (Z_to_bv 64 2305843009213693952)
                (Z_to_bv 64 (fa SB c)) (Z_to_bv 64 1099511627776) (Z_to_bv 64 1152921504607895551)
                (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 1500) (Z_to_bv 64 16140901064495857663) s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0xa6384) fc None m1 (seg_rom asegs))) ->
  evt asegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 stat) (Z_to_bv 64 c) (Z_to_bv 64 CH) (Z_to_bv 64 n)
             a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 gfa_entry) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros HSB Hc ER IC LK ST HLO HLOH HLO2 HSP MI K.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  destruct IC as (IC1 & IC2).
  unfold i_spacebeg, i_premapped, INST, g_instance, gfa_entry, kHighShadowEnd, rinfo, RIS_of, ri_lock in *.
  change (2364504 + 32)%Z with 2364536%Z in IC1. change (2364504 + 56)%Z with 2364560%Z in IC2.
  pose proof (munch_refl [(R, R + 8); (bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 128%nat ST.
  zhide.
  zidle_begin sp 128%Z MUz WMz.
  do 14 zstep.
  zidle_end MUz WMz.
  do 18 zstep.
  replace (SB + 137438953472 + c ≪ 7)%Z with R by (rewrite ER, Z.shiftl_mul_pow2 by lia; lia).
  replace (SB + (c ≪ 32 + 3758096384))%Z with (fa SB c) by (unfold fa, rb; rewrite Z.shiftl_mul_pow2 by lia; lia).
  do 7 zstep.
  zstep. ifF.
  do 2 zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 R) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. rewrite ER. Z.div_mod_to_equations. lia. }
  amo_step AMO.
  zstep. ifF.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  zstep. ifT.
  eapply K; eassumption.
Qed.

(* [comment removed for export] *)
Ltac tr_from0 m0 MU WM H :=
  lazymatch type of MU with munch ?W _ ?mc =>
    apply (rw_cells_transport asegs W m0 mc _ _) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia ]
  end.
Ltac tr_from0a m0 MU WM H :=
  lazymatch type of MU with munch ?W _ ?mc =>
    apply (u32arr_transport asegs W m0 mc _ _) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; lia ]
  end.

Definition gfa_fast_W (sp : word) (R CH n : Z) : list (Z * Z) :=
  [(R, R + 8); (R + 16, R + 24); (R + 72, R + 80); (CH, CH + 4 * n); (bv_unsigned sp - 128, bv_unsigned sp)]%Z.

(* [comment removed for export] *)
Definition gfa_fast_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB c R CH n nfree mfa auser muser : Z) (ws chs : list word) (rand : word) (exh : byte) (pad : list byte)
    (nalloc nfreed r0 r1 r2 r3 lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (gfa_fast_W sp R CH n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ ri_lock m' R 0
    /\ ri_core m' R (nfree - n) mfa auser muser
    /\ ri_tail m' R rand exh pad (nalloc + n) nfreed r0 r1 r2 r3
    /\ u32arr asegs m' CH (dest ws chs (nfree - n) (Z.to_nat n))
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma gfa_fast_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R stat CH n nfree mfa auser muser : Z) (ws chs : list word)
    (rand : word) (exh : byte) (pad : list byte) (nalloc nfreed r0 r1 r2 r3 lo : Z),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (1 <= n <= 16)%Z -> (n <= nfree)%Z -> (4 * nfree <= 4 * Z.of_nat (length ws) <= 2^29)%Z -> length chs = 16%nat ->
  (0 < CH /\ CH + 64 <= ACEIL /\ (CH + 64 <= SB \/ SB + 2^37 + 4096 <= CH))%Z ->
  (0 <= mfa < 2^64)%Z -> (0 <= auser < 2^64)%Z -> (0 <= muser < 2^64)%Z -> (0 <= nalloc < 2^64)%Z ->
  inst_cells SB m -> ri_lock m R 0 -> ri_core m R nfree mfa auser muser -> ri_tail m R rand exh pad nalloc nfreed r0 r1 r2 r3 ->
  fl_arr m SB c ws -> u32arr asegs m CH chs ->
  stk asegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 128)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (gfa_fast_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SB c R CH n nfree mfa auser muser ws chs
               rand exh pad nalloc nfreed r0 r1 r2 r3 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 stat) (Z_to_bv 64 c) (Z_to_bv 64 CH) (Z_to_bv 64 n)
             a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 gfa_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HSB Hc ER Hn Hnf Hws Hchs HCH Hmfa Hau Hmu Hna IC LK RC RT FL CHS ST HLO HLOH HLO2 HSP MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  eapply gfa_head; try eassumption.
  intros m1 junk FR LK1 ST1 MU WM MI1.
  unfold kHighShadowEnd, rinfo, RIS_of, ri_core, ri_tail, fl_arr in *.
  assert (FAB : (SB + 2^32 <= fa SB c /\ fa SB c + 2^29 <= SB + 2^37)%Z) by (unfold fa, rb; lia).
  tr_from0 m MU WM RC. tr_from0 m MU WM RT. tr_from0a m MU WM FL. tr_from0a m MU WM CHS.
  apply (munch_weaken _ (gfa_fast_W sp R CH n)) in MU; [| unfold sub_fp, gfa_fast_W; cbn [outside]; intros; lia].
  unfold gfa_fast_W in MU.
  zhide.
  zstep. zstep. ifF.
  do 2 zstep. zstep. ifF.
  eapply evt_mono; [eapply gfa_tail_spec with (nfree' := (nfree - n)%Z) (ACEIL := ACEIL) (lo := lo) (ra := ra)
     (s0o := s0) (s1o := s1) (s2o := s2) (s3o := s3) (s4o := s4) (s5o := s5) (s6o := s6) (s7o := s7) (s8o := s8)
     (s9o := s9) (s10o := s10) (s11o := s11); try eassumption; try lia | ].
  1:{ eexists. eassumption. }
  intros ms' PO. unfold gfa_Q, gfa_ret_post in PO. destruct_exs PO. destruct PO as (E & MU2 & WM2 & MI2 & LK2 & RT2 & CHS2 & ST2).
  subst ms'. unfold gfa_fast_post. unfold gfa_tail_W in MU2.
  do 15 eexists. split; [reflexivity|].
  split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]; unfold sub_fp, gfa_tail_W, gfa_fast_W; cbn [outside]; intros; lia]|].
  split; [eapply wmono_trans; eassumption|].
  split; [assumption|]. split; [assumption|].
  tr_from0 m0 MU2 WM2 RC.
  split; [exact RC|]. split; [assumption|]. split; assumption.
Qed.
