(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Arr Cells.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout R_small R_thread R_cache_defs F_memset R_imemset.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_R_intalloc () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List=repeat_lengthC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026ImageA5asegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes3nat00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalC45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes8list_indC47Corelib5Lists7ListDef3mapI47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00c69OSSVerify5KrLib2K53A02:R_intalloc@map_unsigned_injC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:R_intalloc?rw_cells_relistC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega=RingMicromega7Formula01C69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init5Logic3iffC47Corelib4Init5Logic3notK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C47Corelib4Init9Datatypes3appC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes9Morphisms?eq_proper_proxyC69OSSVerify5KrLib2K53Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib7Classes9Morphisms:respectfulC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc69OSSVerify5KrLib2K53A02:R_intalloc:wr_at_app2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_addC69OSSVerify5KrLib2K53Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses=iff_ReflexiveC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6repeatC56Stdlib6ZArith4Znat5Z2Nat7inj_addC46Stdlib5Lists4List:repeat_appC46Stdlib5Lists4List9app_nil_rc69OSSVerify5KrLib2K53A02:R_intalloc=rw_cells_app2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC56Stdlib6ZArith4Znat5Z2Nat2idC69OSSVerify5KrLib2K53Lib3ArrAu8arr_of_rw_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:R_intalloc8ia_stateC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:R_intalloc7ia_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib2K53A02:R_intalloc4ia_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4prod00K69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C45stdpp9bitvector;definitions9bv_signedC69OSSVerify5KrLib2K56Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC69OSSVerify5KrLib2K56Common8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C69OSSVerify5KrLib2K53Lib8StepFast8sf_congTC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC69OSSVerify5KrLib2K56Common8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC69OSSVerify5KrLib2K53Lib8StepFast6sf_ad1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_addr_ztobvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_store8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast7sf_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_install_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cb_split_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cb_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC69OSSVerify5KrLib2K53Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC69OSSVerify5KrLib2K53Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast=u8arr_frame_nC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast=munch_write_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast;stk_write_nC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z6shiftlC69OSSVerify5KrLib2K56Common8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC69OSSVerify5KrLib2K56Common8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C69OSSVerify5KrLib2K53Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC69OSSVerify5KrLib2K53Lib3Mem3sxbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3MemAsext_extract_byteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast<sf_load_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr0>K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC69OSSVerify5KrLib2K53Lib6MState:interp_effC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState8step_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib2K53Lib8StepFast<sf_branch_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_cong1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib2K53Lib8StepFast?sf_load8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC69OSSVerify5KrLib2K53Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib4Init9Datatypes4prod01K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C47Corelib5Lists7ListDef5skipnC69OSSVerify5KrLib2K53Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib2K53Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC69OSSVerify5KrLib2K53Lib8StepFast?sf_install_loadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast;sf_evt_stepC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00K4ELinuxProcessSemantics5Riscv5Instr5msize04c69OSSVerify5KrLib2K53A02:R_intalloc9g_ia_wordC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:R_intalloc3IAPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:R_intalloc>intalloc_entryC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C4ELinuxProcessSemantics5Riscv3Sem2w1C69OSSVerify5KrLib2K53Lib6MState6w1_litC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC69OSSVerify5KrLib2K56Common8PropExec6v_andiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4landC69OSSVerify5KrLib2K56Common8PropExec8alu_andiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec6v_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC69OSSVerify5KrLib2K56Common8PropExec8alu_slliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C69OSSVerify5KrLib2K56Common8PropExec6v_sllwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics5Riscv3Sem5low32C69OSSVerify5KrLib2K56Common8PropExec6w_sllwC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC69OSSVerify5KrLib2K53Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0DK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics5Riscv3Sem3eff06C4ELinuxProcessSemantics5Riscv3Sem5is_x0K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff07C69OSSVerify5KrLib2K53Lib3Mem3le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4tgetC69OSSVerify5KrLib2K56Common8PropExec5v_xorC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC69OSSVerify5KrLib2K56Common8PropExec7alu_xorC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C69OSSVerify5KrLib2K56Common8PropExec5v_andC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_andC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0EK4ELinuxProcessSemantics5Riscv3Sem3eff08C69OSSVerify5KrLib2K53Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC4ELinuxProcessSemantics5Riscv7Prelude4tsetC4ELinuxProcessSemantics5Riscv3Sem7reg_getC69OSSVerify5KrLib2K56Common8PropExec6v_srlwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC69OSSVerify5KrLib2K56Common8PropExec6w_srlwC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:R_intalloc@rw_cells_relistZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_luiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C69OSSVerify5KrLib2K56Common8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7w_addiwC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C69OSSVerify5KrLib2K56Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C69OSSVerify5KrLib2K53Lib8StepFast7sf_btgtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast:sf_transMRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028F_memset<memset_postZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029R_imemset<imemset_specC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>store_bytes_1'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_store_goalC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z3injC69OSSVerify5KrLib2K53Lib3ArrArw_cells_of_u8arrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symc69OSSVerify5KrLib2K53A02:R_intalloc?split_repeat_cbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast6sf_ad4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast:sf_evt_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu32C69OSSVerify5KrLib2K53Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr?u8arr_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K53Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr6awidth01I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums8positive00K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init9Datatypes:comparison02C47Corelib4Init3Nat3subC47Corelib4Init9Datatypes7nat_indC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specc69OSSVerify5KrLib2K53A02:R_intalloc>firstn_repeat'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:R_intalloc=skipn_repeat'C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib2K53Lib3Mem=bytes_at_readC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C69OSSVerify5KrLib2K56Common8PropExec6v_srliC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC69OSSVerify5KrLib2K53Lib7ZBridge9zr_shiftrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2K46Stdlib9micromega:ZMicromega;ZArithProof03c69OSSVerify5KrLib2K53A02:R_intalloc>zero_run_read8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3ivlC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01".
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac addr_near k ::=
  let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 512))%Z in
  lazymatch inb with true => idtac end.

Definition intalloc_entry : Z := 0x73c20.
Definition IAP : Z := 0x10de80.              (* [comment removed for export] *)
Definition g_ia_word : Z := 0x19c708.       (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_relist : forall m A cs cs',
  rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' E. split; [split; [exact Hwf'| rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma map_unsigned_inj : forall (l1 l2 : list byte), map (@bv_unsigned 8) l1 = map (@bv_unsigned 8) l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hxy Hl. f_equal; [apply bv_eq; exact Hxy| apply IH; exact Hl].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_relistZ : forall m A cs cs',
  rw_cells asegs m A cs -> cells_wf cs' ->
  map (@bv_unsigned 8) (cells_bytes cs') = map (@bv_unsigned 8) (cells_bytes cs) -> rw_cells asegs m A cs'.
Proof. intros m A cs cs' H Hwf E. apply (rw_cells_relist m A cs cs' H Hwf). apply map_unsigned_inj. exact E. Qed.

Lemma wr_at_app2 : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app2 : forall m A cs1 cs2,
  rw_cells asegs m A (cs1 ++ cs2) <-> rw_cells asegs m A cs1 /\ rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app2 by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

(* [comment removed for export] *)
Lemma split_repeat_cb : forall m A n k (z : byte),
  rw_cells asegs m A [CB (Z.to_nat n) (repeat z (Z.to_nat n))] -> 0 <= k <= n ->
  rw_cells asegs m A [CB (Z.to_nat k) (repeat z (Z.to_nat k))] /\ u8arr asegs m (A + k) (repeat z (Z.to_nat (n - k))).
Proof.
  intros m A n k z H Hk.
  apply (rw_cells_relist _ _ _ ([CB (Z.to_nat k) (repeat z (Z.to_nat k))] ++ [CB (Z.to_nat (n - k)) (repeat z (Z.to_nat (n - k)))])) in H.
  - apply rw_cells_app2 in H. destruct H as [H1 H2]. split; [exact H1|].
    cbn [cells_size csize] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia. exact (u8arr_of_rw_cells _ _ _ _ _ H2).
  - cbn [cells_wf app cell_wf]. rewrite !repeat_length. repeat split; reflexivity || exact I.
  - cbn [cells_bytes app cbytes]. rewrite !app_nil_r, <- repeat_app, <- Z2Nat.inj_add by lia.
    replace (k + (n - k)) with n by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ia_state (b : bool) (m : mem) : Prop :=
  if b then
    rw_cells asegs m g_ia_word [C4 (Z_to_bv 64 1)]
    /\ u8arr asegs m (IAP + 8) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))
  else
    rw_cells asegs m g_ia_word [C4 (Z_to_bv 64 0)]
    /\ (exists j, rw_cells asegs m IAP [C1 j])
    /\ (exists bs, Z.of_nat (length bs) = 0x40000 /\ u8arr asegs m (IAP + 8) bs)
    /\ (exists bs, Z.of_nat (length bs) = 0xd80 /\ u8arr asegs m (IAP + 0x40040) bs)
    /\ (exists bs, Z.of_nat (length bs) = 0x40248 /\ u8arr asegs m (IAP + 0x40dc0) bs)
    /\ (exists j, rw_cells asegs m (IAP + 0x81008) [CB 40 j])
    /\ rw_cells asegs m 0xfdaf0 [C8 (Z_to_bv 64 0x19c720)]
    /\ rw_cells asegs m 0x19c720 [C8 (Z_to_bv 64 4096)].

(* [comment removed for export] *)
Definition ia_W (usp : Z) : list (Z * Z) := [(usp - 48, usp); (g_ia_word, g_ia_word + 4); (IAP, IAP + 0x81030)].

Definition ia_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 IAP) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (ia_W (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ ia_state true m'.

(* [comment removed for export] *)
Lemma intalloc_fast_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  ia_state true m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x662000 <= lo ->
  mem_inv asegs m ->
  evt asegs (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 intalloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros IS ST LO ILO MI.
  destruct IS as (W & MAP).
  unfold g_ia_word, intalloc_entry, IAP in *.
  assert (LMAP : Z.of_nat (length (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))) = 0x40000) by (rewrite repeat_length; lia).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl (ia_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold ia_W, g_ia_word, IAP in MU.
  carve_frame 48%nat ST.
  apply (rw_cells_relist _ _ _ [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]]) in W;
    [| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
  do 11 zstep. ifT.
  do 8 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
  unfold ia_state, g_ia_word, IAP.
  split; [eapply rw_cells_relist; [exact W | vm_compute; repeat split; reflexivity | vm_compute; reflexivity]| exact MAP].
Qed.

(* [comment removed for export] *)
Lemma intalloc_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  ia_state false m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x662000 <= lo ->
  mem_inv asegs m ->
  evt asegs (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 intalloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros IS ST LO ILO MI.
  destruct IS as (W & (j0 & P0) & (j1 & LMAP & MAP) & (j2 & LINFO & INFO) & (j3 & LSEC & SEC) & (j4 & STATS) & GOT & PS).
  unfold g_ia_word, intalloc_entry, IAP in *.
  replace (1105536 + 8) with 1105544 in MAP by reflexivity. replace (1105536 + 262208) with 1367744 in INFO by reflexivity.
  replace (1105536 + 265664) with 1371200 in SEC by reflexivity. replace (1105536 + 528392) with 1633928 in STATS by reflexivity.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl (ia_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold ia_W, g_ia_word, IAP in MU.
  apply (rw_cells_relist _ _ _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]]) in W;
    [| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
  carve_frame 48%nat ST.
  do 11 zstep. ifF.
  do 8 zstep.
  apply (rw_cells_relist _ _ _ [C4 (Z_to_bv 64 0)]) in W; [| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
  assert (AMO : amo_aligned AW (Z_to_bv 64 1689352) = true) by (vm_compute; reflexivity).
  amo_step AMO.
  change (sx32 z64) with (Z_to_bv 64 0).
  do 4 zstep.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  do 3 zstep. ifF.
  apply (rw_cells_relistZ _ _ _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]]) in W;
    [| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
  do 2 zstep. ifF.
  do 8 zstep.
  call (imemset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1633928 0 40 j4).
  all: try assumption; try lia.
  rename POST into STATS2.
  lstep.
  do 5 zstep.
  assert (EL1 : length j1 = Z.to_nat 262144) by (apply Nat2Z.inj; rewrite Z2Nat.id by lia; exact LMAP).
  call (imemset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1105544 0 262144 j1).
  1:{ rewrite <- EL1. apply rw_cells_of_u8arr. exact MAP. }
  all: try assumption; try lia.
  apply u8arr_of_rw_cells in POST. rename POST into MAP2.
  assert (LMAP2 : Z.of_nat (length (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 262144))) = 262144) by (rewrite repeat_length; lia).
  clear EL1 LMAP.
  do 6 zstep.
  assert (EL2 : length j2 = Z.to_nat 3456) by (apply Nat2Z.inj; rewrite Z2Nat.id by lia; exact LINFO).
  call (imemset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1367744 0 3456 j2).
  1:{ rewrite <- EL2. apply rw_cells_of_u8arr. exact INFO. }
  all: try assumption; try lia.
  apply u8arr_of_rw_cells in POST. rename POST into INFO2.
  assert (LINFO2 : Z.of_nat (length (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 3456))) = 3456) by (rewrite repeat_length; lia).
  clear EL2 LINFO.
  do 6 zstep.
  assert (EL3 : length j3 = Z.to_nat 262728) by (apply Nat2Z.inj; rewrite Z2Nat.id by lia; exact LSEC).
  call (imemset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1371200 0 262728 j3).
  1:{ rewrite <- EL3. apply rw_cells_of_u8arr. exact SEC. }
  all: try assumption; try lia.
  destruct (split_repeat_cb _ _ _ 16 _ POST ltac:(lia)) as [SEC16 SECR]. clear POST.
  change (Z.to_nat 16) with 16%nat in SEC16. change (Z.to_nat (262728 - 16)) with (Z.to_nat 262712) in SECR.
  assert (LSECR : Z.of_nat (length (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 262712))) = 262712) by (rewrite repeat_length; lia).
  clear EL3 LSEC.
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true by (vm_compute; reflexivity) end.
  cbv iota.
  do 4 zstep. lstep. lstep.
  zstep. lstep. zstep. lstep.
  do 8 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
  unfold ia_state, g_ia_word, IAP. split.
  - eapply rw_cells_relistZ; [exact W | vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
  - exact MAP2.
Qed.

Lemma skipn_repeat' : forall {X} (z : X) n k, skipn k (repeat z n) = repeat z (n - k).
Proof. intros X z n. induction n as [|n IH]; intros [|k]; cbn; auto. Qed.
Lemma firstn_repeat' : forall {X} (z : X) n k, firstn k (repeat z n) = repeat z (Nat.min k n).
Proof.
ltac2:(KReplay.run1_chk (kr_t_R_intalloc ()) [] "p'0h01kh11ni001nh22k0h32IHh41Xh51zp;1p;3p;2p;8p;4p200R0g01:BR1p4p710p8P0g025HR2p4p710p8P0p1002fp4p710p8g0076j13Tg00<\j32Tg00DYj17Tg00E9j25Tg00VYj14Tg00ESj2<Tg00GSj8;Tg04JLj4:TP1j36TP2j38Tg04Jmj29Tf4R2f3R1f2R3f1R4f0R53638p=119459613p=0g00CPR6%32R7P2P5P2P1P4D1P2P1P5P4C032^06R4X16P6P2P5P2P1g00j4R8D1P2P1P5P8C0527P5%31R7%71'5P1P8P1P3P8D1P1P3P8P8C0527ef5R7#3R9%77'5R:P7%45R;P7P2P8D1P7P2P;P8C0529eX06P5O1n0110000020010100X26P6f6R<#3P<P5P<P7%41R=D1P<P7P5P=C032P5P:P7P8P7P2%43R3D1P7P2P8P3C0529ef7R9#3R3P31<9<R8P8P9P5P9P<P2D1P9P<P5P2C0f8#3\3/58P1P5O1G;P9P;P9P<%42R2D1P9P<P;P2C0523eX06P5O1n0110000020010100X26X34X16P5C:W1X55X40o"). Qed.

(* [comment removed for export] *)
Lemma zero_run_read8 : forall m A N i,
  u8arr asegs m A (repeat (Z_to_bv 8 0) (Z.to_nat N)) -> 0 <= i -> i + 8 <= N ->
  ov_read_bytes asegs m (wa (A + i)) 8 = Some (repeat (Z_to_bv 8 0) 8).
Proof.
  intros m A N i [HB _] Hi HN.
  rewrite (bytes_at_read asegs m A _ i 8 HB Hi) by (rewrite repeat_length; lia).
  f_equal. rewrite skipn_repeat', firstn_repeat'. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma pim_spec : forall (Q : machine_state -> Prop) (m : mem) (p : Z)
    ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
  0 <= p < 2 ^ 47 ->
  u8arr asegs m (IAP + 8) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000)) -> mem_inv asegs m ->
  (forall a1' a2' a3', evt asegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) (Z_to_bv 64 IAP) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6) F (Z_to_bv 64 0x67c74) fc None m (seg_rom asegs))) ->
  evt asegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) (Z_to_bv 64 IAP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x67bd0) fc None m (seg_rom asegs)).
Proof.
  intros until fc. intros HP MAP MI K. unfold IAP in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (E47 : Z.shiftr p 47 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  zstep. rewrite E47. zstep. ifF.
  assert (HQ : 0 <= Z.shiftr p 32 < 32768).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  do 3 zstep.
  assert (SH3 : (p ≫ 32) ≪ 3 = 8 * (p ≫ 32)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite SH3.
  pose proof (zero_run_read8 m (1105536 + 8) 262144 (8 * (p ≫ 32)) MAP ltac:(lia) ltac:(lia)) as RD.
  replace (1105536 + 8 + 8 * (p ≫ 32)) with (1105536 + 8 * (p ≫ 32) + 8) in RD by lia.
  zstep. change (le_bytes_to_word (repeat (Z_to_bv 8 0) 8)) with (Z_to_bv 64 0).
  zstep. zstep. ifT.
  apply K.
Qed.
