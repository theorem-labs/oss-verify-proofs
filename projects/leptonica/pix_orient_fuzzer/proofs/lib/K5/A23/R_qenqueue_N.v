(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of zal_ex, qenq_new_hit_empty_spec replaced by plain proofs). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Arr Walk Image.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import R_small R_m2s R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_quar_defs R_qenqueue.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
Ltac2 kr_t_R_qenqueue_N () := "C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K53A23;R_glue_defs7qcacheTC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53A23;R_glue_defs:qcache_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23<R_qenqueue_N:qnew_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53A23<R_cache_defs:chunk_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_quar_defs3r24C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53A23<R_cache_defs7pc_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs8pc_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs;cstat_allocC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint04K47Corelib4Init7Decimal4uint0;K47Corelib4Init7Decimal4uint03K47Corelib4Init7Decimal4uint0:K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintI47Corelib4Init5Logic3and00c69OSSVerify5KrLib2K53A23<R_qenqueue_N:qnew_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:R_qenqueue9qenq_postC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53A23<R_cache_defs6cacheTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_quar_defs6qfirstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_quar_defs5qlastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_quar_defs6qbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_glue_defs6qchainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_quar_defs>qcache_rep_iffC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs:cptr_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs4cptrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib2K53Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs3boxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs5boxedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflK46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib2K53Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums1Z03c69OSSVerify5KrLib2K53A23<R_qenqueue_N6zal_exC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC69OSSVerify5KrLib2K53Lib6MState:interp_effC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree02C45stdpp9bitvector;definitions9bv_signedC69OSSVerify5KrLib2K56Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC69OSSVerify5KrLib2K53Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC69OSSVerify5KrLib2K56Common8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4tsetC4ELinuxProcessSemantics5Riscv7Prelude4tgetC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics5Riscv3Sem7reg_getC69OSSVerify5KrLib2K53Lib6MState8step_genC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z9add_assocC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC69OSSVerify5KrLib2K56Common8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast6sf_ad1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_addr_ztobvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast7sf_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cb_split_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cb_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffI47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib9micromega;ZifyClasses9and_morphC69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast=munch_write_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC47Corelib4Init5Logic8eq_transK4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC69OSSVerify5KrLib2K53Lib8StepFast<sf_branch_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_cong1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib2K53Lib3Mem4sx32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast<sf_load_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec6v_slliC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C69OSSVerify5KrLib2K56Common8PropExec8alu_slliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C69OSSVerify5KrLib2K53Lib8StepFast8sf_congTC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib2K53Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_store_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C56Stdlib6ZArith6BinInt1Z6shiftlC69OSSVerify5KrLib2K53Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01C69OSSVerify5KrLib2K56Common8PropExec6v_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6shiftrC69OSSVerify5KrLib2K53Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C69OSSVerify5KrLib2K53Lib3Arr;u32arr_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem4zx32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@zext_extract_le4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0FK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv3Sem3eff06C4ELinuxProcessSemantics5Riscv3Sem5is_x0K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff08K4ELinuxProcessSemantics5Riscv3Sem3eff07C69OSSVerify5KrLib2K53Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC69OSSVerify5KrLib2K56Common8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C69OSSVerify5KrLib2K53Lib8StepFast6sf_ad4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23<R_qenqueue_N3zalC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C69OSSVerify5KrLib2K56Common8PropExec5v_luiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C69OSSVerify5KrLib2K53A23;R_prim_defs5unboxC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_quar_defs;batch_of_cbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC69OSSVerify5KrLib2K53Lib8StepFastAsf_store8_direct0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast6sf_ad2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr?u64arr_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr<u64arr_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr<u64arr_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr3updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr:upd_lengthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_glue_defs6qbatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_quar_defs4bsumC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapI47Corelib4Init5Peano2le00C69OSSVerify5KrLib2K53A23;R_quar_defs:qbatch_iffC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init9Datatypes4list02C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic5proj2C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast:sf_evt_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs;shl32_shr30C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237R_small<sx32_small_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC47Corelib5Lists7ListDef5skipnC69OSSVerify5KrLib2K53Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib2K53Lib8StepFast@sf_store8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_install_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast>u32arr_frame_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast;stk_write_nC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_extractC69OSSVerify5KrLib2K53Lib8StepFast?sf_load8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast?sf_install_loadC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04C4ELinuxProcessSemantics5Riscv3Sem7amo_valC69OSSVerify5KrLib2K53Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast>u64arr_frame_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast;sf_evt_stepC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs:i_spacebegC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega8ZifyInst7Inj_Z_ZI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5amoop02C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init7Decimal4uint01C69OSSVerify5KrLib2K53A23:R_qenqueue;qenq_entry'C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C4ELinuxProcessSemantics5Riscv3Sem2w0K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init9Datatypes:comparison02K4ELinuxProcessSemantics5Riscv5Instr6awidth02I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00C69OSSVerify5KrLib2K53Lib6MState6w0_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem2w1C69OSSVerify5KrLib2K53Lib6MState6w1_litC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qnew_cells (m : mem) (T SB cnt mc : Z) (ws24 : list word) (w : word) (stj : word) (jb : list byte) : Prop :=
  pc_cells m (pc_addr T 24) cnt mc 8192 /\ u32arr asegs m (pc_addr T 24 + 16) ws24
  /\ rw_cells asegs m (cstat_alloc T) [C8 stj] /\ rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)]
  /\ rw_cells asegs m (chunk_addr SB 24 w) [CB 8192 jb].

(* [comment removed for export] *)
Definition qnew_after (m : mem) (T SB cnt mc : Z) (ws24 : list word) : Prop :=
  pc_cells m (pc_addr T 24) (cnt - 1) mc 8192 /\ u32arr asegs m (pc_addr T 24 + 16) ws24
  /\ (exists stj, rw_cells asegs m (cstat_alloc T) [C8 stj]) /\ rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)].

(* [comment removed for export] *)
Lemma qenq_new_hit_empty_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (T stack M n SB lo cnt mc : Z) (ws24 : list word) (w stj : word) (jb : list byte),
  (1 <= n <= 2^28)%Z ->
  qcache_rep m (qcacheT T) [] ->
  qnew_cells m T SB cnt mc ws24 w stj jb -> (1 <= cnt <= 16)%Z -> (0 <= mc < 2^31)%Z -> length ws24 = 16%nat ->
  nth_error ws24 (Z.to_nat (cnt - 1)) = Some w ->
  (chunk_addr SB 24 w) mod 8192 = 0%Z -> (chunk_addr SB 24 w + 8192 <= r24 SB + 2^32)%Z ->
  (T + 4096 <= r24 SB \/ r24 SB + 2^32 <= T)%Z -> (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0x785000 <= T)%Z -> (T mod 4096 = 0)%Z -> (0 < SB)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (T + 4096 <= lo)%Z -> (r24 SB + 2^32 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (qenq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
                (chunk_addr SB 24 w, chunk_addr SB 24 w + 8192); (bv_unsigned sp - 64, bv_unsigned sp)]%Z
               (qcacheT T) [(chunk_addr SB 24 w, [(M, n)])] lo m (fun m' => qnew_after m' T SB cnt mc ws24))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (qcacheT T)) (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 stack) (Z_to_bv 64 M)
             (Z_to_bv 64 n) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qenq_entry') fc None m (seg_rom asegs)).
Proof.
  intros until jb. intros Hn QR NC Hcnt Hmc Hlen Hw HB8 HB2 HTS HT0 HT HT4 HSB ST HLO HTl HRl HSP MI.
  destruct NC as (PC & ARR & STA & SBC & JB).
  apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & _). cbn [length qfirst qlast qbytes map last fold_right] in QH.
  unfold qcacheT, cacheT, pc_cells, pc_addr, cstat_alloc, i_spacebeg, INST, g_instance, r24, kHighShadowEnd, qenq_entry' in *.
  change (2280664 + 32)%Z with 2280696%Z in SBC.
  replace (T + 208 + 80 * 24)%Z with (T + 2128)%Z in * by lia. replace (T + 2128 + 16)%Z with (T + 2144)%Z in * by lia.
  pose proof (cptr_range w) as RW.
  remember (chunk_addr SB 24 w) as B eqn:EB.
  assert (HB1 : (SB + 24 * 2^32 <= B)%Z) by (subst B; unfold chunk_addr; lia).
  change (24 * 2^32)%Z with 103079215104%Z in *. change (2^32)%Z with 4294967296%Z in *.
  pose proof (munch_refl [(T + 80, T + 80 + 32); (T + 2128, T + 2128 + 4); (T + 2784, T + 2784 + 8);
                          (B, B + 8192); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (munch_refl [(T + 2128, T + 2128 + 4); (T + 2784, T + 2784 + 8); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUj.
  pose proof (wmono_refl asegs m) as WM.
  apply box in JB.
  carve_frame 64%nat ST.
  zhide.
  do 8 zstep.
  zstep. zstep. ifT.
  zstep. rewrite (sx32_small_A cnt) by lia.
  zstep. ifF.
  do 3 zstep. zstep.
  rewrite (shl32_shr30 (cnt + -1)) by lia.
  do 4 zstep.
  pose proof (u32arr_read asegs _ (T + 2144) ws24 (cnt - 1) w (Z_to_bv 64 (T + 208 + 4 * (cnt + -1) + 1936)) ARR Hw ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. change (zx32 w) with (Z_to_bv 64 (cptr w)). clear RD.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (T + 2784)) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. lia. }
  amo_step AMO.
  do 7 zstep.
  replace (Z.shiftl (cptr w) 4 + (SB + 103079215104))%Z with B by (subst B; unfold chunk_addr; rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. ifF.
  do 4 zstep.
  let mm := amem in
  pose proof (rw_cells_transport asegs _ m mm B _ (unbox _ JB) MUj WM
                ltac:(change (Z.of_nat (cells_size [CB 8192 jb])) with 8192%Z; cbn [disjoint_from]; lia)) as JB'.
  clear MUj JB.
  destruct (batch_of_cb _ _ _ JB') as (w0 & w1 & w2 & bws & BH & BA & BL). clear JB'.
  zstep; fix_lit_store. zstep. zstep; fix_lit_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with TB0 : u64arr asegs mm (B + 24) _ |- _ =>
      pose proof (u64arr_store_ok asegs mm (B + 24) _ 0 (Z_to_bv 64 (B + 24)) TB0 ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as SO;
      pose proof (u64arr_bound asegs mm (B + 24) _ TB0) as HBA;
      zstep;
      pose proof (u64arr_write asegs mm (B + 24) _ 0 (Z_to_bv 64 M) TB0 ltac:(lia)) as TB';
      clear TB0 end end.
  replace (B + 24 + 8 * 0)%Z with (B + 24)%Z in TB' by lia.
  store_done. clear HBA.
  zstep. ifT.
  zstep. zstep; fix_lit_store. zstep.
  do 3 zstep.
  do 8 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk asegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep.
  apply evt_done. unfold qenq_post.
  do 16 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| eassumption]; unfold sub_fp; cbn [outside]; intros; lia|].
  split; [eassumption|]. split; [eassumption|].
  split; [| split; [| eassumption]].
  - apply (proj2 (qcache_rep_iff _ _ _)). cbn [length qfirst qlast qbytes map last fold_right bsum snd fst Z.of_nat]. split.
    + replace (8192 + (n + 0) + 0)%Z with (0 + (n + 8192))%Z by lia. eassumption.
    + cbn [qchain]. split; [| exact I].
      apply (proj2 (qbatch_iff _ _ _ _)). cbn [bsum fold_right snd length Z.of_nat]. split; [| split].
      * replace (8192 + (n + 0))%Z with (n + 8192)%Z by lia. eassumption.
      * eexists. split; [eassumption| split; [rewrite upd_length; exact BL|]].
        destruct bws as [|x bws']; [cbn in BL; lia|]. reflexivity.
      * cbn. lia.
  - unfold qnew_after, pc_cells, pc_addr, cstat_alloc, i_spacebeg, INST, g_instance.
    replace (T + 208 + 80 * 24)%Z with (T + 2128)%Z by lia. replace (T + 2128 + 16)%Z with (T + 2144)%Z by lia.
    split; [eassumption| split; [eassumption| split; [eexists; eassumption| eassumption]]].
Qed.

