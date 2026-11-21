(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of zal_ex, compact_code, compact_of_range, cdealloc_push_spec, cdealloc_drain_A_spec, cdealloc_drain_B_spec replaced by plain proofs). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Arr Walk.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout R_small R_m2s R_thread R_cache_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
Ltac2 kr_t_R_cdealloc () := "C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C35stdpp7tactics<f_equal_helpK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2c69OSSVerify5KrLib2K53A23:R_cdealloc:compact_ofC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53A23<R_cache_defs7pc_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs8pc_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53A23<R_cache_defs4T_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs5SB_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedc69OSSVerify5KrLib2K53A23:R_cdealloc:cdealloc_WC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23:R_cdealloc=cdealloc_postC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib2K53Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z7comparec69OSSVerify5KrLib2K53A23:R_cdealloc6zal_exC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC69OSSVerify5KrLib2K53Lib6MState:interp_effC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC69OSSVerify5KrLib2K56Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC69OSSVerify5KrLib2K53Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC69OSSVerify5KrLib2K56Common8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4tsetC4ELinuxProcessSemantics5Riscv7Prelude4tgetC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics5Riscv3Sem7reg_getC69OSSVerify5KrLib2K53Lib6MState8step_genC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC69OSSVerify5KrLib2K56Common8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast6sf_ad1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_addr_ztobvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_store8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast7sf_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cb_split_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cb_splitC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC69OSSVerify5KrLib2K53Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphC69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init5Logic8eq_transK4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC69OSSVerify5KrLib2K53Lib8StepFast<sf_branch_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_cong1C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr@u32arr_transportC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C69OSSVerify5KrLib2K53Lib8StepFast8sf_congTC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic5proj2C69OSSVerify5KrLib2K56Common8PropExec5v_mulC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC69OSSVerify5KrLib2K56Common8PropExec5m_mulC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BC69OSSVerify5KrLib2K56Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:K46Stdlib9micromega7EnvRing3Pol01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC69OSSVerify5KrLib2K53Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast<sf_load_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C69OSSVerify5KrLib2K53Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7add_0_rC69OSSVerify5KrLib2K53Lib8StepFast6sf_ad4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast?sf_load8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec6v_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC69OSSVerify5KrLib2K56Common8PropExec8alu_slliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C69OSSVerify5KrLib2K56Common8PropExec5v_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast6sf_ad2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec6v_srliC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec8alu_srliC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23:R_cdealloc@compact_of_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC69OSSVerify5KrLib2K53Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_store_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C69OSSVerify5KrLib2K53Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr<u32arr_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr?u32arr_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr<u32arr_writeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC69OSSVerify5KrLib2K53Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem;amo_alignedK4ELinuxProcessSemantics5Riscv5Instr5instr0FK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics5Riscv3Sem3eff06C4ELinuxProcessSemantics5Riscv3Sem5is_x0K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff08K4ELinuxProcessSemantics5Riscv3Sem3eff07C69OSSVerify5KrLib2K53Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr3updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr:upd_lengthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C69OSSVerify5KrLib2K53Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast:sf_evt_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23:R_cdealloc<compact_codeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs;shl32_shr30C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237R_small<sx32_small_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs;cstat_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs6cacheTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC47Corelib5Lists7ListDef5skipnC69OSSVerify5KrLib2K53Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib2K53Lib8StepFast@sf_install_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04C45stdpp9bitvector;definitions:bv_extractC69OSSVerify5KrLib2K53Lib8StepFast?sf_install_loadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7amo_valC69OSSVerify5KrLib2K53Lib8StepFast;sf_evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs:i_spacebegC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2K53A23<R_cache_defs;img_hull_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs;img_hull_hiC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv3Sem2w0C69OSSVerify5KrLib2K53Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5amoop02C69OSSVerify5KrLib2K53A235R_m2s>kHighShadowEndC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs4INSTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23:R_cdealloc>cdealloc_entryC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init9Datatypes:comparison02K4ELinuxProcessSemantics5Riscv5Instr6awidth02I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00C4ELinuxProcessSemantics5Riscv3Sem2w1C69OSSVerify5KrLib2K53Lib6MState6w1_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23:R_cdeallocEcdealloc_drain_A_postC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C69OSSVerify5KrLib2K53Lib8StepFast7sf_btgtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast:sf_transMRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFastAsf_store8_direct0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem4zx32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@zext_extract_le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge?zb_shl_shr_landC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC69OSSVerify5KrLib2K53Lib7ZBridge6zr_divC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs:zx32_smallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs6cstatsC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c69OSSVerify5KrLib2K53A23:R_cdealloc>drainhalf_retBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23:R_cdealloc9rta_entryC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23:R_cdealloc=cdealloc_retDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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

Definition cdealloc_entry : Z := 0xa34d8.
Definition cdealloc_retD : Z := 0xa3688.
Definition drainhalf_retB : Z := 0xa38d0.
Definition rta_entry : Z := 0xa3a10.

(* [comment removed for export] *)
Definition compact_of (SB c p : Z) : Z := (p - SB - c * 2^32) / 16.

Lemma compact_code : forall SB c p, (0 <= c < 2^31)%Z -> (0 <= SB)%Z -> (0 <= p - SB - c * 2^32 < 2^32)%Z ->
  Z.shiftr (Z.land (p + - Z.land (Z.shiftl c 32) 18446744073709551615 + - SB) 18446744073709551615) 4 = compact_of SB c p.
Proof.
  intros SB c p Hc HSB Hp. unfold compact_of. change 18446744073709551615%Z with (Z.ones 64).
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.land_ones (c * 2 ^ 32)) by lia. rewrite Z.mod_small by lia.
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. f_equal; lia.
Qed.

Lemma compact_of_range : forall SB c p, (0 <= p - SB - c * 2^32 < 2^32)%Z -> (0 <= compact_of SB c p < 2^28)%Z.
Proof. intros SB c p Hp. unfold compact_of. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. Qed.

Definition cdealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T SB c p cnt mc cs : Z) (ws : list word) (W : list (Z * Z)) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (stj : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ pc_cells m' (pc_addr T c) (cnt + 1) mc cs
    /\ u32arr asegs m' (pc_addr T c + 16) (upd ws (Z.to_nat cnt) (Z_to_bv 64 (compact_of SB c p)))
    /\ rw_cells asegs m' (cstat_alloc T) [C8 stj]
    /\ rw_cells asegs m' i_spacebeg [C8 (Z_to_bv 64 SB)]
    /\ stk asegs m' lo (bv_unsigned sp).

Definition cdealloc_W (T c : Z) (sp : word) : list (Z * Z) :=
  [(pc_addr T c, pc_addr T c + 4); (pc_addr T c + 16, pc_addr T c + 80); (cstat_alloc T, cstat_alloc T + 8);
   (bv_unsigned sp - 48, bv_unsigned sp)]%Z.

Lemma cdealloc_push_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL T SB c p cnt mc cs lo : Z) (ws : list word) (stj : word),
  (1 <= c <= 31)%Z ->
  (SB + c * 2^32 <= p < SB + c * 2^32 + 2^32)%Z -> ((p - SB - c * 2^32) mod 16 = 0)%Z ->
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  pc_cells m (pc_addr T c) cnt mc cs -> (0 <= cnt < mc)%Z -> (1 <= mc <= 16)%Z -> (0 <= cs < 2^63)%Z ->
  u32arr asegs m (pc_addr T c + 16) ws -> length ws = 16%nat ->
  rw_cells asegs m (cstat_alloc T) [C8 stj] ->
  T_ok ACEIL T -> SB_ok ACEIL SB ->
  stk asegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (cdealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T SB c p cnt mc cs ws (cdealloc_W T c sp) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until stj. intros Hc Hp Hpal SBC PC Hcnt Hmc Hcs ARR Hlen STA HT HSB ST HLO HLOH HLO2 HSP MI.
  destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5). destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4). unfold img_hull_lo, img_hull_hi in HT5.
  unfold kHighShadowEnd in *.
  unfold cdealloc_W, pc_cells, pc_addr, cstat_alloc, cacheT, i_spacebeg, INST, cdealloc_entry, g_instance in *.
  change (2280664 + 32)%Z with 2280696%Z in SBC.
  remember (T + 208 + 80 * c)%Z as P eqn:EP.
  pose proof (munch_refl [(P, P + 4); (P + 16, P + 80); (T + 2784, T + 2784 + 8); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  zidle_begin sp 48%Z MUz WMz.
  do 8 zstep.
  zidle_end MUz WMz.
  ifF.
  do 2 zstep. ifF.
  do 3 zstep.
  replace (T + 208 + c * 80)%Z with P by lia.
  zstep. rewrite (sx32_small_A mc) by lia. zstep. ifF.
  zstep. rewrite (sx32_small_A cnt) by lia. zstep. ifF.
  do 12 zstep.
  rewrite (shl32_shr30 cnt) by lia.
  rewrite (compact_code SB c p) by lia.
  pose proof (compact_of_range SB c p ltac:(lia)) as HCP.
  zstep.
  pose proof (u32arr_store_ok asegs m0 (P + 16) ws cnt (Z_to_bv 64 (P + 4 * cnt + 16)) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SO.
  zstep.
  pose proof (u32arr_write asegs m0 (P + 16) ws cnt (Z_to_bv 64 (compact_of SB c p)) ARR ltac:(lia)) as ARR'.
  replace (P + 16 + 4 * cnt)%Z with (P + 4 * cnt + 16)%Z in ARR' by lia.
  store_done.
  zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (T + 2784)) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. lia. }
  amo_step AMO.
  do 8 zstep.
  release_frame FR ST (bv_unsigned sp).
  finish; unfold pc_addr, cstat_alloc, pc_cells; try rewrite <- EP; try eassumption.
  eapply munch_weaken; [|exact MU]. intros x Hx. cbn in *. lia.
Qed.

(* [comment removed for export] *)
Definition cdealloc_drain_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T c p P mc cs lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 drainhalf_retB) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0' t1' t2' (Z_to_bv 64 P)
                  (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 INST) (Z_to_bv 64 (bv_unsigned sp - 104)) (Z_to_bv 64 (cstats T))
                  (Z_to_bv 64 c) (Z_to_bv 64 (P + 16 + 4 * (mc - mc / 2))) (Z_to_bv 64 (mc / 2)) a6' a7'
                  (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 rta_entry) fc None m' (seg_rom asegs)
    /\ munch [(P, P + 4); (bv_unsigned sp - 112, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ pc_cells m' P (mc - mc / 2) mc cs
    /\ rw_cells asegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp - 112) [CB 8 junk; C8 (Z_to_bv 64 INST); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                                 C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cdealloc_retD)]
    /\ stk asegs m' lo (bv_unsigned sp - 112).

Lemma cdealloc_drain_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL T c p mc cs lo : Z),
  (1 <= c <= 31)%Z ->
  pc_cells m (pc_addr T c) mc mc cs -> (2 <= mc <= 16)%Z -> (0 <= cs < 2^63)%Z ->
  T_ok ACEIL T ->
  stk asegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 112)%Z ->
  (bv_unsigned sp <= 2^47)%Z -> (0 <= p < 2^64)%Z ->
  mem_inv asegs m ->
  evt asegs (cdealloc_drain_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T c p (pc_addr T c) mc cs lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hc PC Hmc Hcs HT ST HLO HLOH HLO2 HSP Hp MI.
  destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5). unfold kHighShadowEnd in *.
  unfold pc_cells, pc_addr, cstats, cacheT, INST, cdealloc_entry, drainhalf_retB, rta_entry, cdealloc_retD, g_instance in *.
  remember (T + 208 + 80 * c)%Z as P eqn:EP.
  pose proof (munch_refl [(P, P + 4); (bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  zidle_begin sp 48%Z MUz WMz.
  do 8 zstep.
  zidle_end MUz WMz.
  ifF.
  do 2 zstep. ifF.
  do 3 zstep.
  replace (T + 208 + c * 80)%Z with P by lia.
  zstep. rewrite (sx32_small_A mc) by lia. zstep. ifF.
  zstep. rewrite (sx32_small_A mc) by lia. zstep. ifT.
  do 7 zstep.
  carve_frame 64%nat ST.
  do 2 zstep.
  zstep; fix_lit_store.
  zstep; fix_lit_store.
  zstep; fix_lit_store.
  zstep. rewrite (sx32_small_A mc) by lia.
  zstep. rewrite (zx32_small mc) by lia.
  zstep; fix_lit_store.
  zstep; fix_lit_store.
  zstep; fix_lit_store.
  zstep; fix_lit_store.
  do 3 zstep.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
  replace (Z.land mc 4294967295) with mc by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
  zstep. ifF.
  do 11 zstep.
  replace (P + Z.shiftl (mc + - (mc / 2)) 2 + 16)%Z with (P + 16 + 4 * (mc - mc / 2))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (bv_unsigned sp + -104)%Z with (bv_unsigned sp - 104)%Z by lia.
  replace (bv_unsigned sp + -112)%Z with (bv_unsigned sp - 112)%Z in * by lia.
  replace (bv_unsigned sp + -48)%Z with (bv_unsigned sp - 48)%Z in * by lia.
  finish; try rewrite <- EP; try eassumption.
Qed.

(* [comment removed for export] *)
Lemma cdealloc_drain_B_spec : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s0o s1o s2o s3o s4o rao : word) (junk : list byte)
    (ACEIL T SB c p cnt mc cs lo : Z) (ws : list word) (stj : word),
  (1 <= c <= 31)%Z ->
  (SB + c * 2^32 <= p < SB + c * 2^32 + 2^32)%Z -> ((p - SB - c * 2^32) mod 16 = 0)%Z ->
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  pc_cells m (pc_addr T c) cnt mc cs -> (0 <= cnt < mc)%Z -> (1 <= mc <= 16)%Z -> (0 <= cs < 2^63)%Z ->
  u32arr asegs m (pc_addr T c + 16) ws -> length ws = 16%nat ->
  rw_cells asegs m (cstat_alloc T) [C8 stj] ->
  T_ok ACEIL T -> SB_ok ACEIL SB ->
  rw_cells asegs m (bv_unsigned sp - 48) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  rw_cells asegs m (bv_unsigned sp - 112) [CB 8 junk; C8 (Z_to_bv 64 INST); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                          C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cdealloc_retD)] ->
  stk asegs m lo (bv_unsigned sp - 112) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 160)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (cdealloc_post rao sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc T SB c p cnt mc cs ws
               [(pc_addr T c, pc_addr T c + 4); (pc_addr T c + 16, pc_addr T c + 80); (cstat_alloc T, cstat_alloc T + 8);
                (bv_unsigned sp - 160, bv_unsigned sp)]%Z lo m)
    (MS (mkR (Z_to_bv 64 drainhalf_retB) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2 (Z_to_bv 64 (pc_addr T c))
             (Z_to_bv 64 (cacheT T)) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p)
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 drainhalf_retB) fc None m (seg_rom asegs)).
Proof.
  intros until stj. intros Hc Hp Hpal SBC PC Hcnt Hmc Hcs ARR Hlen STA HT HSB FR FR1 ST HLO HLOH HLO2 HSP MI.
  destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5). destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4). unfold img_hull_lo, img_hull_hi in HT5.
  unfold kHighShadowEnd in *.
  unfold pc_cells, pc_addr, cstat_alloc, cacheT, i_spacebeg, INST, drainhalf_retB, cdealloc_retD, g_instance in *.
  change (2280664 + 32)%Z with 2280696%Z in SBC.
  remember (T + 208 + 80 * c)%Z as P eqn:EP.
  pose proof (munch_refl [(P, P + 4); (P + 16, P + 80); (T + 2784, T + 2784 + 8); (bv_unsigned sp - 160, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z in * by lia.
  replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z in * by lia.
  zhide.
  do 3 zstep.
  carve_frame 48%nat ST.
  zstep.
  zstep. zstep; try fix_lit_store. zstep. zstep. zstep; try fix_lit_store.
  zstep. ifT.
  do 6 zstep.
  release_frame FR0 ST (bv_unsigned sp + -112)%Z.
  do 3 zstep.
  release_frame FR1 ST (bv_unsigned sp + -48)%Z.
  do 4 zstep.
  zstep. rewrite (sx32_small_A cnt) by lia.
  zstep.
  do 12 zstep.
  rewrite (shl32_shr30 cnt) by lia.
  rewrite (compact_code SB c p) by lia.
  pose proof (compact_of_range SB c p ltac:(lia)) as HCP.
  zstep.
  pose proof (u32arr_store_ok asegs m0 (P + 16) ws cnt (Z_to_bv 64 (P + 4 * cnt + 16)) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SO.
  zstep.
  pose proof (u32arr_write asegs m0 (P + 16) ws cnt (Z_to_bv 64 (compact_of SB c p)) ARR ltac:(lia)) as ARR'.
  replace (P + 16 + 4 * cnt)%Z with (P + 4 * cnt + 16)%Z in ARR' by lia.
  store_done.
  zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (T + 2784)) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. lia. }
  amo_step AMO.
  do 8 zstep.
  release_frame FR ST (bv_unsigned sp).
  finish; unfold pc_addr, cstat_alloc, pc_cells; try rewrite <- EP; try eassumption.
  eapply munch_weaken; [|exact MU]. intros x Hx. cbn in *. lia.
Qed.
