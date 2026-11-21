(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of zal_ex, comballoc_hit_spec replaced by plain proofs). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Arr Walk.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout R_small R_m2s R_cache_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import R_classid.
Import ListNotations.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
Ltac2 kr_t_R_comballoc () := "C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K52AG;R_sizeclass7ClassIDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs7pc_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs8pc_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53B23<R_cache_defs;cstat_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs4T_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs5SB_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K52AG;R_sizeclass=ClassID_propsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass9ClassSizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23;R_comballocBcomballoc_hit_postC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib2K53Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z7comparec69OSSVerify5KrLib2K53B23;R_comballoc6zal_exC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC69OSSVerify5KrLib2K56Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC69OSSVerify5KrLib2K56Common8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC69OSSVerify5KrLib2K53Lib8StepFast6sf_ad1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_addr_ztobvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_store8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast7sf_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cb_split_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cb_splitC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffK46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07I47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses9and_morphC69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast=munch_write_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib2K56Common8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zC45stdpp9bitvector;definitions7bv_wrapC69OSSVerify5KrLib2K53Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge;v_sltiu_b2zC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C69OSSVerify5KrLib2K56Common8PropExec9alu_sltiuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C69OSSVerify5KrLib2K53Lib8StepFast8sf_congTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C69OSSVerify5KrLib2K56Common8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC69OSSVerify5KrLib2K56Common8PropExec8alu_xoriC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib2K53Lib8StepFast<sf_branch_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_cong1C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic5proj2C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z6shiftlC69OSSVerify5KrLib2K56Common8PropExec5v_luiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC69OSSVerify5KrLib2K56Common8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C69OSSVerify5KrLib2K53B239R_classid<classid_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B239R_classid@classid_35x_specC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC69OSSVerify5KrLib2K56Common8PropExec5v_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC69OSSVerify5KrLib2K56Common8PropExec5m_mulC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BK46Stdlib9micromega7EnvRing3Pol01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC69OSSVerify5KrLib2K53Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast<sf_load_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC69OSSVerify5KrLib2K56Common8PropExec6v_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC69OSSVerify5KrLib2K56Common8PropExec8alu_slliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib2K53Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_store_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07K46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib2K53Lib8StepFast6sf_ad2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec6v_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6shiftrC69OSSVerify5KrLib2K53Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr;u32arr_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem4zx32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@zext_extract_le4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC69OSSVerify5KrLib2K53B23<R_cache_defs4cptrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr0FK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC69OSSVerify5KrLib2K53Lib6MState:interp_effC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics5Riscv3Sem3eff06C4ELinuxProcessSemantics5Riscv3Sem5is_x0K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff08K4ELinuxProcessSemantics5Riscv3Sem3eff07C69OSSVerify5KrLib2K53Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4tgetC4ELinuxProcessSemantics5Riscv3Sem7reg_getC69OSSVerify5KrLib2K53Lib6MState8step_genC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib8StepFast6sf_ad4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast?sf_load8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C69OSSVerify5KrLib2K53B23<R_cache_defs:cptr_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC69OSSVerify5KrLib2K53B23<R_cache_defs:chunk_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs;shl32_shr30C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237R_small<sx32_small_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge<zb_lxor_onesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs6cacheTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t03K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib2K56Common8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C47Corelib5Lists7ListDef5skipnC69OSSVerify5KrLib2K53Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib2K53Lib8StepFast@sf_install_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib2K53Lib9StoreFast>u32arr_frame_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast;stk_write_nC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05K46Stdlib9micromega=RingMicromega5Psatz04C45stdpp9bitvector;definitions:bv_extractC69OSSVerify5KrLib2K53Lib8StepFast?sf_install_loadC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7amo_valC69OSSVerify5KrLib2K53Lib8StepFast;sf_evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs:i_spacebegC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2K53B23<R_cache_defs;img_hull_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs;img_hull_hiC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op203K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics5Riscv3Sem2w0C69OSSVerify5KrLib2K53Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5amoop02C69OSSVerify5KrLib2K53B235R_m2s>kHighShadowEndC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs4INSTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23;R_comballoc?comballoc_entryC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init9Datatypes:comparison02K4ELinuxProcessSemantics5Riscv5Instr6awidth02I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00C4ELinuxProcessSemantics5Riscv3Sem2w1C69OSSVerify5KrLib2K53Lib6MState6w1_litC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
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
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition comballoc_entry : Z := 0xa59e4.

Definition comballoc_hit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T SB c cnt mc cs : Z) (ws : list word) (w : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (stj : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (chunk_addr SB c w)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(pc_addr T c, pc_addr T c + 4); (cstat_alloc T, cstat_alloc T + 8); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ pc_cells m' (pc_addr T c) (cnt - 1) mc cs
    /\ u32arr asegs m' (pc_addr T c + 16) ws
    /\ rw_cells asegs m' (cstat_alloc T) [C8 stj]
    /\ rw_cells asegs m' i_spacebeg [C8 (Z_to_bv 64 SB)]
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma comballoc_hit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL T SB size cnt mc cs lo : Z) (ws : list word) (w stj : word),
  (1 <= size <= 65536)%Z ->
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  pc_cells m (pc_addr T (ClassID size)) cnt mc cs -> (1 <= cnt <= 16)%Z -> (0 <= mc < 2^31)%Z -> (0 <= cs < 2^63)%Z ->
  u32arr asegs m (pc_addr T (ClassID size) + 16) ws -> length ws = 16%nat -> nth_error ws (Z.to_nat (cnt - 1)) = Some w ->
  rw_cells asegs m (cstat_alloc T) [C8 stj] ->
  T_ok ACEIL T -> SB_ok ACEIL SB ->
  stk asegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (comballoc_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T SB (ClassID size) cnt mc cs ws w lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 size) (Z_to_bv 64 8)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 comballoc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until stj. intros Hsz SBC PC Hcnt Hmc Hcs ARR Hlen Hw STA HT HSB ST HLO HLOH HLO2 HSP MI.
  pose proof (ClassID_props size Hsz) as [Hc Hcsz].
  set (c := ClassID size) in *.
  destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5). destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  unfold kHighShadowEnd in *.
  unfold pc_cells, pc_addr, cstat_alloc, cacheT, i_spacebeg, INST, comballoc_entry, g_instance in *.
  pose proof (munch_refl [(T + 208 + 80 * c, T + 208 + 80 * c + 4); (T + 2784, T + 2784 + 8); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  change (2364504 + 32)%Z with 2364536%Z in SBC.
  remember (T + 208 + 80 * c)%Z as P eqn:EP.
  carve_frame 48%nat ST.
  zhide.
  do 7 zstep.
  do 2 zstep.
  rewrite (proj2 (Z.ltb_ge size 1)) by lia. cbn [Z.b2z]. rewrite Z.add_0_r.
  do 2 zstep. rewrite zb_lxor_ones by lia. ifT.
  do 3 zstep. ifT.
  do 2 zstep. ifF.
  zstep. ifF.
  (* [comment removed for export] *)
  eapply evt_cut; [apply classid_35x_spec; [lia| assumption]|].
  intros ms' (t0' & t1' & a2' & a4' & a5' & a6' & a7' & ->). fold c.
  zstep. ifF.
  do 2 zstep. ifF.
  do 3 zstep.
  replace (T + 208 + c * 80)%Z with P by lia.
  zstep. rewrite (sx32_small_A cnt) by lia.
  zstep. ifF.
  do 7 zstep.
  rewrite (shl32_shr30 (cnt + -1)) by lia.
  zstep.
  pose proof (u32arr_read asegs m0 (P + 16) ws (cnt - 1) w (Z_to_bv 64 (P + 4 * (cnt + -1) + 16)) ARR Hw ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. change (zx32 w) with (Z_to_bv 64 (cptr w)). clear RD.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (T + 2784)) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. lia. }
  amo_step AMO.
  do 7 zstep. ifT.
  do 8 zstep.
  replace (Z.shiftl (Z.land (cptr w) 18446744073709551615) 4 + (Z.shiftl c 32 + SB))%Z with (chunk_addr SB c w).
  2:{ unfold chunk_addr. pose proof (cptr_range w). change 18446744073709551615%Z with (Z.ones 64).
      rewrite Z.land_ones, Z.mod_small by lia. rewrite !Z.shiftl_mul_pow2 by lia. lia. }
  release_frame FR ST (bv_unsigned sp).
  finish; unfold pc_addr, cstat_alloc, pc_cells; try rewrite <- EP; try eassumption.
Qed.
