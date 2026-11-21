(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of qcb_k1 and qcbrec_prim_spec replaced by leptonica/kernel_fuzzer's plain proofs, addresses mapped). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Arr Walk Image.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import R_small R_m2s R_thread.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_poison R_deallocate R_qput R_combfree R_qdorec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_R_qcbrec () := "C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z4lxorK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib2K53B23<R_deallocate;land255_lowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_deallocate8lxor_lowC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K53B23<R_cache_defs5SB_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_glue_defs3ru8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_poison8ps_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_thread<thread_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subK69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238R_qcbrec5qcb_WC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238R_qcbrec9qcb_afterC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238R_qcbrec;qcbrec_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_thread9tsd_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC69OSSVerify5KrLib2K53B236R_qput:ru8'_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236R_qput4ru8'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs3boxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs5boxedC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53B238R_poison:ps_args_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_poison=ps_shad_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7comparec69OSSVerify5KrLib2K53B238R_qcbrec6zal_exC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC69OSSVerify5KrLib2K53Lib6MState:interp_effC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC69OSSVerify5KrLib2K56Common8PropExec6v_andiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions7bv_wrapC69OSSVerify5KrLib2K53Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC69OSSVerify5KrLib2K56Common8PropExec8alu_andiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4tsetC4ELinuxProcessSemantics5Riscv7Prelude4tgetC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics5Riscv3Sem7reg_getC69OSSVerify5KrLib2K53Lib6MState8step_genC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec6v_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC69OSSVerify5KrLib2K53Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C69OSSVerify5KrLib2K56Common8PropExec8alu_slliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C69OSSVerify5KrLib2K53Lib8StepFast8sf_congTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec6v_sllwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C69OSSVerify5KrLib2K56Common8PropExec6w_sllwC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=K46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2c69OSSVerify5KrLib2K53B238R_qcbrec9hdr_cas30C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_deallocate:hdr3_to_c4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0DK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv3Sem3eff06C4ELinuxProcessSemantics5Riscv3Sem5is_x0K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff07K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib2K53Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_andC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_andC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC69OSSVerify5KrLib2K53Lib8StepFast<sf_branch_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_cong1C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2C69OSSVerify5KrLib2K56Common8PropExec5v_xorC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC69OSSVerify5KrLib2K53Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_xorC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C69OSSVerify5KrLib2K53Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0EK4ELinuxProcessSemantics5Riscv3Sem3eff08C35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib2K53Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC69OSSVerify5KrLib2K53Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib9micromega;ZifyClasses6eq_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses9and_morphC69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast=munch_write_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast;stk_write_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_deallocate:c4_to_hdr3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238R_qcbrec3zalC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem4zx16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@zext_extract_le2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast<sf_load_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C69OSSVerify5KrLib2K53Lib8StepFast7sf_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem4zx32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@zext_extract_le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec4v_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC69OSSVerify5KrLib2K56Common8PropExec6alu_orC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C69OSSVerify5KrLib2K53Lib8StepFast7sf_btgtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast:sf_transMRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs5unboxC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_poison?ps_cells_framedC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC69OSSVerify5KrLib2K53B238R_poisonApoison_small_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_poisonApoison_small_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatK47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_thread:frame_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs9gcts_specC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC56Stdlib6ZArith6BinInt1Z9add_assocC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib2K53Lib8StepFast6sf_ad1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_addr_ztobvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast?sf_load8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstC69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_store_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C69OSSVerify5KrLib2K53Lib8StepFast;sf_pair_eq1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast;sf_pair_eq2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_install_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib2K53B23:R_combfree:rtail_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_combfree?rtail_frag_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_glue_defs5farunC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236R_qput@roundup8_machineC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237R_small<sx32_small_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_deallocate7land_m4C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega=RingMicromega5Psatz05C4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC69OSSVerify5KrLib2K53Lib8StepFast?sf_install_loadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast;sf_evt_stepC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_thread9g_tsd_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_thread7pth_tsdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_threadBg_pthread_tsd_mainC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w0C69OSSVerify5KrLib2K53Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr6awidth01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI47Corelib4Init5Logic4True00C69OSSVerify5KrLib2K53B235R_m2s>kHighShadowEndC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs:i_spacebegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_thread3tpAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs4INSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_thread@g_tsd_key_initedC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr5aluop03I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop06C4ELinuxProcessSemantics5Riscv3Sem2w1K47Corelib4Init9Datatypes:comparison02K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5aluop09C69OSSVerify5KrLib2K53B23<R_cache_defs;img_hull_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs;img_hull_hiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C69OSSVerify5KrLib2K53Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_depot_defs<dep_disj_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass9ClassSizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_glue_defs3lchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs4tsepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass?ClassSize_rangeC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr05K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03C69OSSVerify5KrLib2K53B23<R_cache_defs4T_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238R_qcbrec=qcbrec_prim_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_store8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cb_split_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cb_splitC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC69OSSVerify5KrLib2K56Common8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC69OSSVerify5KrLib2K56Common8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C69OSSVerify5KrLib2K53B23:R_combfree8gbb_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_combfree=gbb_frag_specC1?~~~~~~~~~~~~~~~C35stdpp4base7or_commC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z<divide_transC56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09C56Stdlib6ZArith6BinInt1Z<divide_add_rC56Stdlib6ZArith6BinInt1Z<divide_mul_rC69OSSVerify5KrLib2K53Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Image>ro_cells_imageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib2FP9bv_lit_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@ro_cells_read_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat7add_0_rc69OSSVerify5KrLib2K53B238R_qcbrecCqthread_cells_frameC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K53B23:R_prim_kit7rwc_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c69OSSVerify5KrLib2K53B238R_qcbrec6qcb_k1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC47Corelib5Lists7ListDef5skipnC69OSSVerify5KrLib2K53Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK4ELinuxProcessSemantics5Riscv5Instr6awidth02C69OSSVerify5KrLib2K53B238R_qdorec<qcbrec_entryC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom3Mon00C69OSSVerify5KrLib2K53B23:R_combfree7gbb_pc1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236Layout@K_kAllocBegMagicC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_qdorec>cdealloc_entryC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_R_qcbrec ()) [] "h04__x1h11rh21Hh32Hkh47__arithh54__ffh66__sat0h78__varmaph85__with91kh:1qh;1xp;2p;3p;1p;4p;6p;8p;7g0000j28Tg000Lj22Tg000lj30Tg001Fj23Tg001cj27Tg002@j25Tg002]j2CTg003Nj21Tg003jj1=Tg004Jj1<Tg004jj2;Tg005Hj1:Tg005fj19Tg006Qj2LTg0074j2KTg007Wj44Tg008Bj1JTg008dj6ITg009Hj8BTg009lj2@Tg00:Nj2ATg00:hj2?Tg00;Tj3>Tg00<3j4DTg00<ej3ETg00=Fj6FTg00=bj4GTg00><j7HTf1R0g00>`R1g00??R2P2g00?_R3f0R4g00@?FHp=6g00@_R5g00A=R6f2R7'8f3R8,27=050P5f4R9f5R:/34/78505X:51589P51289159:,3:/749059X151C891168116:f6R;,2:,16[[g00A[R:#=%<:1;50%:5%95R:P1P2P2P3P51L56R<g00BGg00Bn,K5R=C4,6:%J2P:P1P2P2P3P5P=g00CSP<C4,6:EIGB1@:3P4P7g00D:R:g00DZR3'A1?47=0:3dA>560CDb5b7b8X051864A0506g00E:[[^05P4P;P8O2b4b69E89P7P4EFCGW2W3X15X;5W9o"). Qed.
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
Lemma hdr_cas30 : forall b, (0 <= b < 256)%Z ->
  (Z.land (3 + 256 * b) 255 = 3 /\ Z.lxor (3 + 256 * b) 3 = 0 + 256 * b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_R_qcbrec ()) [] "h07__arithh14__ffh28__varmaph35__with44__p1h54__x1h62Hbh71bh81zp;2p;1p;3p;4p;6p;8p;7p100EWp4p7210g00FCR0p4p710p8g003Nj24Tg00Faj10Tg00GFj1;Tg0000j26Tg00Gdj27Tg00H?j11Tg001Fj2?Tg001cj25Tg00Hdj2ETg000lj33Tg00IBj2>Tg003jj1ATg004Jj1@Tg00I`j1TTg005Hj1STg005fj1RTg006Qj2<Tg007Wj48Tg009lj2MTg00:Nj2=Tg00:hj2JTg00;Tj3ITg00<3j4FTg004jj2GTg0074j2HTg00J>j6DTg008Bj1KTg009Hj8LTg00Jbj4CTg00Kfj7BTP0j6NTg00Lgj4OTg00><j7PTg00MBj7QTg00@_R0f1R1g00Mff0R2C8p=9P1g00>`R3g00??R4P4g00?_R5P2g00@?FPp=2f2R6P3P4P4P5P1P2FQp=:g00A=R7/42R8g00BnR9#0#0#0#0#0#0#0#0#;R:,62'7%19R;#;R<1?:1R='5R>%1;#1#1#1#1#1#;'E=30<1>><R>157=R;530P<P1g00A[R?#AR@%@?R?%T0RA%S0RB%R0RC1<07RD1<0<RE'9,2CP0PEg00BGRE1<0:RFC8,2C3:1MC5RGP2P6g00D:RHg00DZRI'=1J26=3HIdAI071CFRIb1b2b3147<16<:'7P2b0RHp-0RJP@P?1G01PBPCP3P4P4P51H09,9D,2CR9PCP3P4P4P5f3ED5:C%K4P9GLPGPIb1b2b3X50W417811471[^50^4JP2166:P6P1O3b0RJCCP01><</5=1?:6,579302X801=0;P>P<P1P<PHPJPHP@P?PAPB19DD,2CP0PDPEPFC8,2C5:CPGPIb1b2b31477167:'7P2b0FBENCOW6X70o"). Qed.

(* [comment removed for export] *)
Definition qcb_W (M n T sp : Z) : list (Z * Z) :=
  [(M, M + 4); (shad (M + 16), shad (M + 16) + ru8 n / 8); (T + 2840, T + 2856); (sp - 112, sp)]%Z.

(* [comment removed for export] *)
Definition qcbrec_post (rao sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (cache c blk : Z) (W : list (Z * Z)) (lo : Z) (P : mem -> Prop) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR rao sp gp tp t0' t1' t2' s0o s1o (Z_to_bv 64 cache) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 blk)
                  a4' a5' a6' a7' s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 cdealloc_entry) fc None m'
             (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ P m' /\ stk asegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition qcb_after (M n b1 T rf rfd : Z) (m : mem) : Prop :=
  rw_cells asegs m M [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)]
  /\ rw_cells asegs m (shad (M + 16)) [CB (Z.to_nat (ru8 n / 8)) (farun (ru8 n / 8))]
  /\ rw_cells asegs m (T + 2840) [C8 (Z_to_bv 64 (rf + 1)); C8 (Z_to_bv 64 (rfd + n))].

(* [comment removed for export] *)
Lemma qcb_k1 : forall ra0 sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
    (rao s0o s1o s2o s3o s4o : word) (ACEIL SB c off M n b1 TCX T rf rfd cache CBP lo : Z) (shj : list byte),
  (1 <= c <= 30)%Z -> (0 <= off < 2^32)%Z -> SB_ok ACEIL SB ->
  (SB <= M)%Z -> (M + 16 + ru8 n <= SB + 2^37)%Z -> (M mod 16 = 0)%Z -> (1 <= n < 2^32)%Z -> (0 <= b1 < 256)%Z ->
  rw_cells asegs m M [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)] ->
  rw_cells asegs m (shad (M + 16)) [CB (Z.to_nat (ru8 n / 8)) shj] -> ps_cells m ->
  thread_cells TCX T m ->
  (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (TCX + 0xa0 <= 0x7fff8000 \/ kHighShadowEnd < TCX)%Z ->
  (TCX + 0xa0 <= 0x10000 \/ 0x79a000 <= TCX)%Z ->
  (0 < T)%Z -> (T + 4096 <= lo)%Z -> (T + 4096 <= 0x7fff8000 \/ kHighShadowEnd < T)%Z -> (T + 4096 <= 0x10000 \/ 0x79a000 <= T)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  (M + 16 <= TCX + 152 \/ TCX + 160 <= M)%Z -> (M + 16 <= T + 2840 \/ T + 2856 <= M)%Z ->
  rw_cells asegs m (T + 2840) [C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 rfd)] ->
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] -> rw_cells asegs m CBP [C8 (Z_to_bv 64 cache)] -> (0 <= cache < 2^64)%Z ->
  (bv_unsigned sp <= CBP)%Z -> (CBP + 8 <= 2^47)%Z ->
  rw_cells asegs m (bv_unsigned sp - 48) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  stk asegs m lo (bv_unsigned sp - 48) -> (lo <= bv_unsigned sp - 112)%Z -> (ACEIL <= lo)%Z -> (0x10007fff8000 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (qcbrec_post rao sp gp (Z_to_bv 64 tpA) s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc cache c (SB + c * 2^32 + off)
               (qcb_W M n T (bv_unsigned sp)) lo (qcb_after M n b1 T rf rfd) m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp - 48)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 CBP) (Z_to_bv 64 M) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (SB + c * 2^32 + off)) (Z_to_bv 64 INST) (Z_to_bv 64 (2^37)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa36ac) fc None m (seg_rom asegs)).
Proof.
  intros until shj. intros Hc Hoff HSBo HM1 HM2 HM16 Hn Hb1 HD SH PS TC HTCX0 HTCXl HTCXs HTCXi HT0 HTl HTs HTi HTX HMX HMT STS SBC CBC
    HCA HCB1 HCB2 FR ST HLO HAC HLOs HSP MI.
  pose proof HSBo as (HSB1 & HSB2 & HSB3 & HSB4). unfold kHighShadowEnd in *.
  destruct TC as [(KI & K0 & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, i_spacebeg, INST, g_instance in *.
  pose proof (ru8'_range n ltac:(lia)) as RU. change (ru8' n) with (ru8 n) in RU.
  apply box in PS. apply box in SBC. apply box in CBC. apply box in STS. apply box in TT.
  apply box in HTCXs. apply box in HTCXi. apply box in HTs. apply box in HTi. apply box in HTX. apply box in HMX. apply box in HMT.
  assert (PA : ps_args_ok (M + 16) (ru8 n)).
  { unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd. split; [split; [Z.div_mod_to_equations; lia| lia]| right; lia]. }
  pose proof (ps_shad_range _ _ PA) as (SR1 & SR2 & SR3 & SR4). unfold kHighShadowEnd in SR2.
  destruct RU as (RU1 & RU2 & RU3). apply box in RU2. apply box in SR3. apply box in HSB2. apply box in PA.
  apply box in HCA. apply box in HCB1. apply box in HCB2. apply box in Hc. apply box in Hoff.
  pose proof (munch_refl (qcb_W M n T (bv_unsigned sp)) m) as MU.
  pose proof (munch_refl [(M, M + 4); (shad (M + 16), shad (M + 16) + ru8 n / 8); (bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MUa.
  pose proof (wmono_refl asegs m) as WM.
  unfold qcb_W in MU.
  assert (RM : (17594333495295 < M < 2^47)%Z) by lia.
  replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z in * by lia.
  (* [comment removed for export] *)
  zhide.
  do 4 zstep.
  do 2 zstep.
  assert (ESH : (Z.land (Z.shiftl M 3) 18446744073709551615 mod 32 = 0)%Z).
  { clear - RM HM16. unfold zal in HM16. rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615%Z with (Z.ones 64).
    rewrite Z.land_ones by lia. rewrite (Z.mod_small (M * 2 ^ 3) (2 ^ 64)) by lia.
    change (2 ^ 3)%Z with 8%Z. Z.div_mod_to_equations; lia. }
  rewrite ESH. fold_reg 14%Z. fold_reg 13%Z.
  rewrite land_m4 by (clear - RM; lia). replace (4 * (M / 4))%Z with M by (clear - RM HM16; unfold zal in HM16; Z.div_mod_to_equations; lia).
  pose proof (hdr_cas30 b1 Hb1) as (HC1 & HC2).
  apply (hdr3_to_c4 _ _ 3 b1 [C4 (Z_to_bv 64 n)]) in HD; [| lia| lia].
  assert (AMO : amo_aligned AW (Z_to_bv 64 M) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. Z.div_mod_to_equations; lia. }
  amo_step AMO. rewrite (sx32_small_A (3 + 256 * b1)) by lia.
  zstep. rewrite ?HC1. zstep. ifF.
  do 3 zstep. rewrite ?HC1, ?HC2.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  apply (c4_to_hdr3 _ _ 0 b1 [C4 (Z_to_bv 64 n)]) in HD; [| lia| lia].
  clear ESH HC1 HC2 AMO. apply box in HM16.
  (* [comment removed for export] *)
  do 7 zstep.
  rewrite (Z.mod_small n 4294967296) by lia. rewrite roundup8_machine by lia. change (ru8' n) with (ru8 n).
  zstep. zstep.
  let mm := amem in
  pose proof (ps_cells_framed m mm _ (unbox _ PS) MUa WM ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)) as PSm.
  clear PS.
  sp_facts.
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (M + 16)%Z (ru8 n) 250 lo shj).
  all: rewrite ?Esp in *; try lia; try exact (unbox _ PA); try eassumption; try (unfold kHighShadowEnd; lia).
  (* [comment removed for export] *)
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_transport asegs _ m mm _ _ (unbox _ TT) MUa WM
                  ltac:(pose proof (unbox _ HMX); pose proof (unbox _ HTCXs); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia))
      as TTm end.
  clear TT.
  call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  all: rewrite ?Esp in *; try lia; try eassumption.
  all: lazymatch goal with
       | |- thread_cells _ _ _ =>
           unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
           split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TTm]
       | |- evt _ _ _ => idtac
       end.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_transport asegs _ m mm _ _ (unbox _ STS) MUa WM
                  ltac:(pose proof (unbox _ HMT); pose proof (unbox _ HTs); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia))
      as STSm;
    pose proof (munch_refl [(T + 2840, T + 2856)]%Z mm) as MUb; pose proof (wmono_refl asegs mm) as WMb end.
  clear STS MUa. clear TTm KI K0 TS T0.
  do 8 zstep.
  apply box in HD. apply box in PC.
  do 2 zstep.
  pose proof (unbox _ Hc) as Hc'. pose proof (unbox _ Hoff) as Hoff'. pose proof (unbox _ HCA) as HCA'.
  pose proof (unbox _ HCB1) as HCB1'. pose proof (unbox _ HCB2) as HCB2'.
  zstep. ifF.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_transport asegs _ m mm _ _ (unbox _ SBC) MU WM
                  ltac:(pose proof (unbox _ HTi); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as SBCm;
    pose proof (rw_cells_transport asegs _ m mm _ _ (unbox _ CBC) MU WM
                  ltac:(pose proof (unbox _ HCB1); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as CBCm;
    match goal with MUb' : munch _ ?m3 mm, WMb' : wmono _ ?m3 mm |- _ =>
      pose proof (rw_cells_transport asegs _ m3 mm _ _ (unbox _ HD) MUb' WMb'
                    ltac:(pose proof (unbox _ HMT); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as HDm;
      pose proof (rw_cells_transport asegs _ m3 mm _ _ (unbox _ PC) MUb' WMb'
                    ltac:(pose proof (unbox _ HTs); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as PCm end end.
  clear SBC CBC HD PC MUb WMb.
  rewrite (Z.mod_small n 4294967296) in STSm by lia.
  change (856024 + 32)%Z with i_spacebeg in SBCm.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_mono; [eapply (rtail_frag_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm (Z_to_bv 64 CBP)
                                s0o s1o s2o s3o s4o rao ACEIL SB cache c off lo); try eassumption; try lia|] end.
  - rewrite unsigned_lit by lia. exact CBCm.
  - intros ms' (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU' & WM' & MI' & ST').
    unfold qcbrec_post, cdealloc_entry. exists t0', t1', t2', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU']; intros xx _; exact I]|].
    split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [| exact ST'].
    unfold qcb_after. lazymatch goal with MU1 : munch [] ?m1 m', WM1 : wmono _ ?m1 m' |- _ =>
      split; [apply (rw_cells_transport asegs _ m1 m' _ _ HDm MU1 WM1 I)|];
      split; [apply (rw_cells_transport asegs _ m1 m' _ _ PCm MU1 WM1 I)|];
      replace (rfd + n)%Z with (n + rfd)%Z by lia; apply (rw_cells_transport asegs _ m1 m' _ _ STSm MU1 WM1 I) end.
Qed.


(* [comment removed for export] *)
Lemma qthread_cells_frame : forall TCX T W (m m' : mem), thread_cells TCX T m -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W img_hull_lo (img_hull_hi - img_hull_lo) -> disjoint_from W (TCX + 0x98) 8 -> thread_cells TCX T m'.
Proof.
ltac2:(KReplay.run1 (kr_t_R_qcbrec ()) [] "h07__arithh14__ffh28__varmaph35__with41Hh51xh61mh72H1h82H2h91Kh:2KIh;2MUh<1Th=2T0h>3TCXh?2TSh@2TThA1WhB2WMhC2m'hD1nhE1yp;1p;3p;2p;4p;8p;:p;7p;<p;Bg004Jj1[Tg00Faj11Tg00NMj1VTg00Nkj1\Tg00ONj1gTg00V9j3FTg00^^j2WTg00H?j1CTg00GFj17Tg001cR0j20Tg003jj1UTg00naj3KTg03Odj3HTg00X]j2YTg02_2j32Tg00RFj2TTg03Gdj1dTg00W:j4DTg01fQj1bTg00GdR1j2:Tg00h`j1?Tg01jkR2j1>Tg00I`j1aTg005Hj1`Tg005fj1_Tg009lj2^Tg00:Nj2]Tg00:hj2rTg000lj3qTg00;Tj3pTg00<3j4oTg003NR3j23Tg01l=j1lTg01l[j4kTg03N;j3ITg03OAj3fTg01m>j4QTg04Dij8PTg03ZMj1OTg03`@l:JTg00Lgj4RTg00Y:j1eTg02f5j3XTg006Qj2hTg007Wj4iTg00><j7jTg03X]l<cTg03YBlBmTg03Yhl<nTf0R4#1#1p=G%C4#1p=6g03bDR5f2R6f1R7'T#e;X4p=4g03c<R8P6P7P4CDp=8AX574p=ZP8P7g03d4P4CDp=NP8P7g03e2P4CDp=@P8P7g03enR9P4CDp=E%14#C#1#1p=B%14#Cp=A%14#1#1#1p=9%C4#Cp==g00@_R:/h4p=;P6g00>`g00??R;P;g00?_R;P:P7g00MfP4Cig00@?Fjp=<1]:4p=5g03o=R<P:P:P:P2P2f5R2f4R=f3R>P6P7P4M<cp=SP:P:P:P:P:P:P0P4P7P6P0P>P=P2f6R0f7R?f8R@f9RAMBmp=LP:P:P3P?P3P0P2P=P>P6P7P4M<np=Mg04D4#[g00BnR3#GRB#1RC#1#GRD#VRE#\%VCRF#\#g[RGAF=>7P11W26%CB#6#G#7RH,02%U5R594E=586AK=>6AH8=>g04@NRIg04AR/YIRJ52010AHRK%7CRC52?f:RL?FA0[[[[P41W?=P1P8P2g046<RM%73RN,TF#d/Z5RFCDg00A=RO,TE#b/Z5RP,N2A4E95R9,@2A4E@5RQ,E2':':A80KQAK@?0AH8@?A2LIJf;RQf=RK/0HRR;2Cf>RS?FKL[[[[[P4P8P?PMPFCD1N@P1@@9A4EQ5,E@':':P11NAP1@A9f<R@=4E5RM,EA':A8LRMAK@QLAH8@QA2SIJf?RMfARR/0HRA;2CfBR??FRS[[[[[P41NQP1@@9A4EM5,E@':P11@K9f@R1=4E5R@,EKA8SA@AK1MSAH81MA2?IJfCR@fERA/0H;2CfFRK?FA?[[[[[P41@M9A4E@5RM,E1fD/0H=8RMAK@?RAH8@?A2AIJfHRJ/0H=2KC%13#B#A#9#=#G#6#9#7RI=8AFR@%13#B#A#9#=#G#6#B#7R?=8APRR%=3#A#=#A#=#=#6#B#9#7RM%=3#6#A#6#B#6#B#9#7R1=4E5R958ARQfIRT=4E5RU98A1RV':RW':RX':10THRHA4EJ5R558AP@PXP8fGRXPKPAPIPFPSP>P6PX%GD#9#9#7RD%=3#6#A#6#6#9#9#9#7R3/YDRSPIg03n^#?R@#>REP7g00A[RY#URZ%[YRY%a:R[%`:R\%_:R]%;DR^%;IR_3<1^];R;P4P6g00D:R`g00DZRa']1r46=q`adAp:O7CoROb1b2b313DIP4b010IERa10DSR`'310INRb/3`RcP4X5:Rd1374#lXE:X5:RePaPbPdPdPdP:P:g04;=1074Ck#5X6:XD:RbPIPI%5IPEPNPdPd%>4#5X5<R<P@PN%5NESM:LP`P`%5`REGMPZPYP[P\%;N9I:_%;3=f:^9I:^R35<]P;POb1b2b3PcP4b0CQGP%OF#>92XIeM:JPRPWP8PXPKPAP?PPPLP>P6PXPDPSP?%?@#?#?R@#>RLP7PZPYP[P\%;?RW9<]^P;POb1b2b313D?P4b010?LRR/3`%7BRB,0?RI/3`RFPdPePRPIPdPdPdPbP?P?%5?PLPBPdPdP<P@PB%5BESM:LP`P`PEGMPZPYP[P\%;B9I:W=<]3P;POb1b2b3PFP4b0CQGP%OP#>92X?eM:JPQPVP8PXPKPAPMP9P0P>P6PXPDPSPM%?@#?#?#?R@#>R0P7PZPYP[P\%;MRV9<]^P;POb1b2b313DMP4b010M0RQ/3`10MCR?/3`RPPdPePQP?PdPdPdPbPMPM%5MP0PCPdPdP<P@PC%5CESR@M:LP`P`PEGMPZPYP[P\%;CR<9I:V=<]3P;POb1b2b3PPP4b0CQGPA2XM0e%O9#>92XMeM:JP8PXPKPAP1PUP2P>P6PXPDPSP1P0P7PZPYP[P\%;1RS9<]^P;POb1b2b313D1P4b01010RD/3`101CR^/3`R2PdPePDP^PdPdPdPbP1P1%51P0PCP@M:LP`P`PEGMPZPYP[P\AI:S<=<]3P;POb1b2b3P2P4b0CQGP%OU#>92X1eM:JCRCRCRP8PXPKPAPHP5P=P>P6P4M:JCRAFTJAeW8W7WBW;W@W=W?P7P4O2n2001000000121000000W4W9P7P4O2n2001000000121000000W4W:P7P4O2n2001000000121000000W4P7P4O2n2001000000121000000W4XCGW6WAX<:X>:o"). Qed.

(* [comment removed for export] *)
Definition qcbrec_prim_W (blk M n T sp : Z) : list (Z * Z) := (blk, blk + 8)%Z :: qcb_W M n T sp.

(* [comment removed for export] *)
Lemma qcbrec_prim_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c idx d mu n b1 TCX T rf rfd cache CBP lo : Z) (shj : list byte),
  (1 <= c <= 30)%Z -> (0 <= idx)%Z -> (d = 0 \/ 16 <= d)%Z -> (d + 16 + ru8 n <= ClassSize c)%Z ->
  ((idx + 1) * ClassSize c <= mu <= 0xE0000000)%Z ->
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB); C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (SB + 2^37))] ->
  rw_cells asegs m (SB + 2^37 + 128 * c + 48) [C8 (Z_to_bv 64 mu)] -> SB_ok ACEIL SB ->
  ((SB + c * 2^32 + idx * ClassSize c + d) mod 16 = 0)%Z -> (1 <= n < 2^32)%Z -> (0 <= b1 < 256)%Z ->
  rw_cells asegs m (SB + c * 2^32 + idx * ClassSize c + d)
    [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)] ->
  (d <> 0 -> lch m (SB + c * 2^32 + idx * ClassSize c) (SB + c * 2^32 + idx * ClassSize c + d))%Z ->
  rw_cells asegs m (shad (SB + c * 2^32 + idx * ClassSize c + d + 16)) [CB (Z.to_nat (ru8 n / 8)) shj] -> ps_cells m ->
  thread_cells TCX T m -> tsep ACEIL SB T TCX ->
  rw_cells asegs m (T + 2840) [C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 rfd)] ->
  rw_cells asegs m CBP [C8 (Z_to_bv 64 cache)] -> (0 <= cache < 2^64)%Z -> (bv_unsigned sp <= CBP)%Z -> (CBP + 8 <= 2^47)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 112)%Z -> (ACEIL <= lo)%Z -> (0x10007fff8000 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  let blk := (SB + c * 2^32 + idx * ClassSize c)%Z in
  evt asegs (qcbrec_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc cache c blk
               (qcbrec_prim_W blk (blk + d) n T (bv_unsigned sp)) lo
               (fun m' => qcb_after (blk + d) n b1 T rf rfd m' /\ (d <> 0 -> rw_cells asegs m' blk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (blk + d))]))%Z
               m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 CBP) (Z_to_bv 64 (blk + d)) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qcbrec_entry) fc None m (seg_rom asegs)).
Proof.
  intros until shj. intros Hc Hidx Hd Hdn Hmu SBC RI HSBo HM16 Hn Hb1 HD LCH SH PS TC TSEP STS CBC HCA HCB1 HCB2 ST HLO HAC HLOs HSP MI blk.
  change (SB + c * 2 ^ 32 + idx * ClassSize c)%Z with blk in HM16, HD, LCH, SH.
  pose proof (ClassSize_range c ltac:(lia)) as [[HCS1 HCS2] HCS3]. apply box in HCS3.
  assert (EIDX : ((idx + 1) * ClassSize c = idx * ClassSize c + ClassSize c)%Z) by ring.
  assert (HIX : (0 <= idx * ClassSize c)%Z) by nia.
  assert (HBK : (SB + c * 2^32 <= blk /\ blk + ClassSize c <= SB + c * 2^32 + 2^32)%Z) by (unfold blk; lia).
  clear EIDX.
  pose proof TSEP as (TOK & HTCX0 & HTCXA & HTCXi & HTSB & HTCXSB & HTX & HTs & HTCXs). destruct TOK as (HT0 & HT4k & HTA & HA47 & HTi).
  apply box in HT4k. apply box in HM16.
  apply box in HTCXi. apply box in HTSB. apply box in HTCXSB. apply box in HTX. apply box in HTs. apply box in HTCXs. apply box in HTi.
  apply box in PS. apply box in TC. apply box in STS. apply box in CBC. apply box in SH.
  pose proof HSBo as (HSB1 & HSB2 & HSB3 & HSB4). apply box in HSB2. unfold kHighShadowEnd in *.
  pose proof (ru8'_range n ltac:(lia)) as (RU1 & RU2 & RU3). change (ru8' n) with (ru8 n) in RU1, RU2, RU3. apply box in RU2.
  unfold i_spacebeg, INST, g_instance, qcbrec_entry in *.
  pose proof (munch_refl [(blk, blk + 8); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU0.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUs.
  pose proof (wmono_refl asegs m) as WM0.
  carve_frame 48%nat ST.
  zhide.
  do 7 zstep. do 4 zstep.
  eapply evt_cut; [eapply (gbb_frag_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ ACEIL SB c idx d mu);
                   try eassumption; lia|].
  intros ms1 (a2' & a3' & a4' & a5' & a6' & a7' & E1). subst ms1.
  unfold gbb_pc1.
  change (SB + c * 2 ^ 32 + idx * ClassSize c)%Z with blk.
  remember (blk + d)%Z as M eqn:EM.
  pose proof Hd as Hd'. apply box in Hd'.
  apply or_comm in Hd.
  destruct Hd as [Hd16| Hd0];
    [ (* [comment removed for export] *)
      zstep; ifF
    | (* [comment removed for export] *)
      zstep; ifT;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (LCHc : d <> 0%Z -> rw_cells asegs mm blk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 M)]) by (intros H; congruence) end ].
    assert (Hblk8 : (blk mod 8 = 0)%Z).
    { pose proof (unbox _ HSB2) as E1. pose proof (unbox _ HCS3) as E2.
      assert (D1 : (8 | SB)%Z) by (apply (Z.divide_trans _ (2^16)); [exists 8192%Z; reflexivity| apply Z.mod_divide; [lia| exact E1]]).
      assert (D2 : (8 | ClassSize c)%Z) by (apply (Z.divide_trans _ 32); [exists 4%Z; reflexivity| apply Z.mod_divide; [lia| exact E2]]).
      apply Z.mod_divide; [lia|]. unfold blk. apply Z.divide_add_r; [apply Z.divide_add_r; [exact D1| exists (c * 2^29)%Z; ring]|].
      apply Z.divide_mul_r. exact D2. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (rw_cells_transport asegs _ m mm _ _ (LCH ltac:(lia)) MUs WM0 ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia))
        as LCm end.
    clear MUs.
    unfold lch in LCm. try rewrite <- EM in LCm.
    zstep.
    let mm := amem in
    let bs := eval vm_compute in (option.default [] (image_bytes asegs 0x10498 8)) in
    assert (RCM : ro_cells asegs mm 0x10498 [CB (length bs) bs])
      by (apply ro_cells_image; [eassumption| vm_compute; reflexivity| lia| cbn; lia]).
    cbn [length] in RCM.
    zstep. fold_reg 14%Z. clear RCM.
    assert (AMOb : amo_aligned AD (Z_to_bv 64 blk) = true).
    { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. exact Hblk8. }
    unfold K_kAllocBegMagic in LCm.
    amo_step AMOb.
    zstep. first [ifF| dIf_closed].
    amo_step AMOb; try fix_lit_store.
    zstep. first [ifF| dIf_closed].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (LCHc : d <> 0%Z -> rw_cells asegs mm blk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 M)]) by (intros _; exact LCm) end.
    clear LCm.
  (* [comment removed for export] *)
  all: assert (PA : ps_args_ok (M + 16) (ru8 n));
         [ unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd; try unfold zal in *; split; [split; [pose proof (unbox _ HM16); try unfold zal in *; Z.div_mod_to_equations; lia| pose proof (unbox _ RU2); lia]| right; lia]|].
  all: pose proof (ps_shad_range _ _ PA) as (SR1 & SR2 & SR3 & SR4); unfold kHighShadowEnd in SR2.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         pose proof (rw_cells_transport asegs _ m mm _ _ (unbox _ SH) MU0 WM0
                       ltac:(cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia)) as SHm;
         pose proof (ps_cells_framed m mm _ (unbox _ PS) MU0 WM0 ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)) as PSm;
         pose proof (qthread_cells_frame _ _ _ m mm (unbox _ TC) MU0 WM0 ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)
                       ltac:(pose proof (unbox _ HTCXSB); cbn [disjoint_from]; lia)) as TCm;
         pose proof (rw_cells_transport asegs _ m mm _ _ (unbox _ STS) MU0 WM0
                       ltac:(pose proof (unbox _ HTSB); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as STSm;
         pose proof (rw_cells_transport asegs _ m mm _ _ (unbox _ CBC) MU0 WM0
                       ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as CBCm end.
  all: lazymatch goal with H : rw_cells asegs ?mm ?A [C8 ?w0; C8 ?w1; C8 ?w2] |- _ =>
         pose proof (proj1 (rwc_app asegs mm A [C8 w0] [C8 w1; C8 w2]) H) as (SB1m & _) end.
  all: change (856024 + 32)%Z with i_spacebeg in SB1m.
  all: assert (HMX : (M + 16 <= TCX + 152 \/ TCX + 160 <= M)%Z)
         by (pose proof (unbox _ HTCXSB) as H0; pose proof (unbox _ Hd') as H1; clear - H0 H1 EM HBK Hdn RU1 Hc Hn HSB1 HIX HCS1 HCS2; lia).
  all: assert (HMT : (M + 16 <= T + 2840 \/ T + 2856 <= M)%Z)
         by (pose proof (unbox _ HTSB) as H0; pose proof (unbox _ Hd') as H1; clear - H0 H1 EM HBK Hdn RU1 Hc Hn HSB1 HIX HCS1 HCS2; lia).
  all: apply box in HMX; apply box in HMT.
  all: pose proof (unbox _ HM16) as HM16'; try rewrite <- EM in HM16'.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply evt_mono; [eapply (qcb_k1 _ sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm ra s0 s1 s2 s3 s4 ACEIL SB c
                                     (idx * ClassSize c) M n b1 TCX T rf rfd cache CBP lo shj); try eassumption; try lia|] end.
  all: try (unfold kHighShadowEnd; lia).
  all: intros ms' (q0 & q1 & q2 & q4 & q5 & q6 & q7 & q3 & q8 & q9 & q10 & m' & E & MU' & WM' & MI' & P & ST').
  all: exists q0, q1, q2, q4, q5, q6, q7, q3, q8, q9, q10, m'; split; [exact E|].
  all: split; [eapply munch_trans; [eapply munch_weaken; [| exact MU0]| eapply munch_weaken; [| exact MU']];
               intros xx Hx; clear - Hx; unfold qcbrec_prim_W, qcb_W in *; cbn [outside] in *; lia|].
  all: split; [eapply wmono_trans; eassumption|]. all: split; [exact MI'|]. all: split; [| exact ST'].
  all: split; [exact P|].
  all: intros Hdnz; pose proof (unbox _ Hd') as Hdd; pose proof (unbox _ HTSB) as HTSB'.
  all: lazymatch goal with |- rw_cells _ ?m2 _ _ => match goal with MU1 : munch _ ?m1 m2, WM1 : wmono _ ?m1 m2 |- _ =>
         apply (rw_cells_transport asegs _ m1 m2 _ _ (LCHc Hdnz) MU1 WM1) end end.
  all: unfold qcb_W; cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia.
Qed.
