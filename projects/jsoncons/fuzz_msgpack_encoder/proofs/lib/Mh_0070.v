(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Mh_0070_blobs1 Mh_0070_blobs2.
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0070 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z7compareI46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00I46Stdlib9micromega7EnvRing5PExpr00C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z3addI46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega7EnvRing5PExpr04I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic3and00K46Stdlib9micromega=RingMicromega5Psatz07I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC46Stdlib9micromega:ZMicromega=Zeval_formulaK4ELinuxProcessSemantics5Riscv5Instr5instr0BI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr0:C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01I47Corelib4Init9Datatypes4prod00C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions;bv_unsignedK4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions9bv_signedC4ELinuxProcessSemantics5Riscv7Prelude4sextK4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv5Instr5instr07K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z6to_natc59OSSVerify5KrLib7Mh_00707VdWkDgC4dclsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC47Corelib4Init5Logic9False_indI47Corelib4Init5Peano2le00C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3mulC49OSSVerify5KrLib8PropExec5v_mulC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem2waC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem4sx32C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells6cbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells5csizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells7cell_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem:length_le4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree02K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_srlC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le1C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_extractC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:munch_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:wmono_reflC1?~~~~~~~~~~~~~~~C46Stdlib5Arith;Compare_dec9le_lt_decI47Corelib4Init6Specif7sumbool00C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr>u8arr_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC49OSSVerify5KrLib8PropExec5m_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec7alu_srlC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_andC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv3Sem4core01C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_frameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6insideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_1'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr:upd_lengthC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib5Arith8PeanoNat3Nat6eq_decK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z:ones_equivC56Stdlib6ZArith6BinInt1Z3ltbC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge8bv_ltu_ZC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith4Znat5Nat2Z8inj_succC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib7Mh_00707VdWkDgC9dcls_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmul_le_mono_pos_rC47Corelib4Init5Logic5proj2c59OSSVerify5KrLib7Mh_00707VdWkDgC8rw2_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame7outsideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6sub_fpC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame<munch_weakenC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge8bv_eqb_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMem8sx32_ztbC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib7SFModel<mod64_land63C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega6VarMap4findK46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega6VarMap1t02C46Stdlib9micromega5Tauto7eval_bfK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega6VarMap1t03C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr5u8arrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5wmonoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr3updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics5Riscv5Instr5instr00I46Stdlib9micromega:ZMicromega;ZArithProof00I4ELinuxProcessSemantics5Riscv3Sem4core00C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I47Corelib4Init5Logic4True00K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv3Sem2w0K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1N01C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00708VdWkDg2C3dvkC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02I46Stdlib9micromega7EnvRing3Pol00K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib;setoid_ring<Ring_polynom5PExpr05K4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv5Instr5instr09C4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv5Instr5instr0;C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_mulhuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1Z7mod_1_rI46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C49OSSVerify5KrLib8PropExec7v_remuwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_divuwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_sllC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM4hideC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu32C49OSSVerify5KrLib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7w_remuwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_sllC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rc59OSSVerify5KrLib7Mh_00707VdWkDgC5tk_nzC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC56Stdlib6ZArith6BinInt1ZBmul_le_mono_nonnegc59OSSVerify5KrLib7Mh_00707VdWkDgC8rw1_walkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:shiftl_0_lC56Stdlib6ZArith6BinInt1Z7add_0_lc59OSSVerify5KrLib7Mh_00707VdWkDgC:loop2_walkC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7m_mulhuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6mod_lec59OSSVerify5KrLib7Mh_00708VdWkDg2C9remuw_valC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7w_divuwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00708VdWkDg2C9divuw_valC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC56Stdlib6ZArith6BinInt1Z9div_smallK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z:mul_div_leK47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_00597WdWkKit=swrap32_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqK46Stdlib;setoid_ring<Ring_polynom5PExpr07C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK4ELinuxProcessSemantics5Riscv5Instr5mulop08K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5mulop04K4ELinuxProcessSemantics5Riscv5Instr5mulop06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I46Stdlib;setoid_ring<Ring_polynom3Mon00C45stdpp9bitvector;definitions5bv_eqK4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr01C49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le8C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocc59OSSVerify5KrLib7Mh_00708VdWkDg3C7dg_postC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_subwC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame9stk_carveC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells;cb_split_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cb_splitC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem:length_le8C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8load_u64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step9wa_of_varC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6w_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM;swrap32_oppC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC49OSSVerify5KrLib8PropExec5b_luiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_commC59OSSVerify5KrLib7Mh_00597WdWkKit<land_W_smallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDgC8dcls_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00708VdWkDg2C:kloop_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6ret_pcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;stk_releaseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec7evt_cutC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:shiftl_1_lC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge?zb_shl_shr_landC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3stkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame9stk_writeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5aluop02C4ELinuxProcessSemantics5Riscv3Sem2w1C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w1_litC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK46Stdlib;setoid_ring<Ring_polynom5PExpr03C56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09K4ELinuxProcessSemantics5Riscv5Instr5instr0QK4ELinuxProcessSemantics5Riscv5Instr5instr0LK46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr08K4ELinuxProcessSemantics5Riscv5Instr5instr02K4ELinuxProcessSemantics5Riscv5Instr5instr0IC49OSSVerify5KrLib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC59OSSVerify5KrLib5VdTab3VDT3kcwC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP8fcvt_d_wC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP6fmul_dC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP8fcvt_w_dC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4rgetc59OSSVerify5KrLib7Mh_00706VdWkGC6g_postC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP4frm0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM;swrap32_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM8land_W64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM<swrap32_lsubC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Image>ro_cells_imageC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8ro_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP9bv_lit_eqC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@ro_cells_read_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem7with_pcC4ELinuxProcessSemantics5Riscv3Sem6accrueC4ELinuxProcessSemantics5Riscv3Sem4fsetK4ELinuxProcessSemantics5Riscv3Sem3eff01C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;interp_eff0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lift_resultC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4execC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP<rmode_staticC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP=exec_fcvt_d_wC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP;frm0_accrueC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?mul_mod_distr_rC56Stdlib6ZArith6BinInt1Z;shiftl_landC56Stdlib6ZArith6BinInt1Z7mod_modC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_mulC4ELinuxProcessSemantics5Riscv3Sem4fgetC59OSSVerify5KrLib5VdTab3VDT8kc_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5VdTab3VDT3s32C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP6fari_dC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP9rmode_dynC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP;exec_fari_dC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4rsetC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP=exec_fcvt_w_dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5VdTab3VDT9tabf_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5VdTab3VDT9tabe_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM:swrap32_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulC59OSSVerify5KrLib6VdMath3VDM4mulrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM<prod32_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z?mul_mod_idemp_rC59OSSVerify5KrLib6VdMath3VDM<land_hi_maskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM9mulr_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM8mulr_lb1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM9mulr_lb62C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM7mulr_ubC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkGC:land_W_M32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6mod_eqC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC79OSSVerify5KrLib2CJ3Lib7Mh_00453Tac7sum_natC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00453TacArw_cells_split_CBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00453Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMem<rw_cells_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c59OSSVerify5KrLib7Mh_00708VdWkDg3C7dg_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;ret_pc_evenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDgC8dcls_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM:mulr_partsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM;mul_machineC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkKit;mulhu_pre32C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP=freg_get_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP>freg_get_otherC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FPCbvmap_set_set_same'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FPBbvmap_set_set_commC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Fpu9fp_of_intC47Corelib4Init9Datatypes3sndC4ELinuxProcessSemantics5Riscv3Fpu;fflags_bitsC56Stdlib6ZArith6BinInt1Z3lorC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP7fari_flC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Fpu9fp_to_intC4ELinuxProcessSemantics5Riscv3Fpu:fmt_doubleK4ELinuxProcessSemantics5Riscv3Fpu5rmode01I4ELinuxProcessSemantics5Riscv3Fpu6fflags00K4ELinuxProcessSemantics5Riscv5Instr6fariop03K4ELinuxProcessSemantics5Riscv3Fpu5rmode04K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty06K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty01K4ELinuxProcessSemantics5Riscv5Instr4ffmt02I4ELinuxProcessSemantics5Riscv3Sem3eff00I4ELinuxProcessSemantics5Riscv3Fpu5rmode00C59OSSVerify5KrLib5VdTab3VDT5TABFwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5VdTab3VDT5TABEwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5VdTab3VDT6TABF_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5VdTab3VDT6TABE_AC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K4ELinuxProcessSemantics5Riscv5Instr5instr0RC49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@div_mul_cancel_lC56Stdlib6ZArith6BinInt1Z8mul_commC59OSSVerify5KrLib7Mh_00258WdSfBase=lor_shift_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_1_lc59OSSVerify5KrLib7Mh_00706VdWkGC=grisu_c2_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_lorC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr6fmvdir01K4ELinuxProcessSemantics5Riscv5Instr5aluop09K46Stdlib9micromega=RingMicromega5Psatz01c59OSSVerify5KrLib7Mh_00707VdWkGpC8dn_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkGpC8lpA_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkGpC8lpB_walkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9pow_add_rC49OSSVerify5KrLib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsI59OSSVerify5KrLib7Mh_01348WdWkFmtF4fgeo00C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_wfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem5wr_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells;cells_bytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8WdWkFmtU4ndigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01348WdWkFmtH3FR4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj6C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj7C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut5fileCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01118WdWkFmtE6isdigbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01348WdWkFmtF6fst_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00658WdWkFmtB8limbs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr<u32arr_boundC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>ro_cells_frameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr<u32arr_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib7SFModel;signed_of_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMem>rw_cells_take3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01348WdWkFmtH6epost1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem9upd_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01348WdWkFmtH;efirst_walkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01348WdWkFmtH4eoutC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem@upd_bytes_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMemAswrap32_landW_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01348WdWkFmtZ=pad_dead_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr?u8arr_transportC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr@u32arr_transportC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01348WdWkFmtF?rw_cells2_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_subC59OSSVerify5KrLib7Mh_01117WdWkOut<fwritex_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01348WdWkFmtF=upd_bytes_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8bytes_atC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr6u32arrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameBro_cells_transportC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I59OSSVerify5KrLib7Mh_01117WdWkOut5fjunk00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut6zflagsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison02C56Stdlib6ZArith6BinInt1Z3minC59OSSVerify5KrLib7Mh_01348WdWkFmtF4pfxbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00658WdWkFmtD6ndigm1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib7Mh_01348WdWkFmtF8pfxb_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8min_specC59OSSVerify5KrLib7Mh_01348WdWkFmtF8pfx_walkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01348WdWkFmtG;fstyle_walkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01348WdWkFmtZ8fin_walkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00658WdWkFmtD<ndigm1_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00708WdWkFmtI;estyle_walkC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityC59OSSVerify5KrLib7Mh_01347WdGnumB2zsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026WdLibc3WDL4gnumC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdWkFmtZc9fmtfp_retC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC59OSSVerify5KrLib7Mh_00658WdWkFmtC4lowzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00658WdWkFmtB?limbs_ok_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00658WdWkFmtR9fmtD_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdWkFmtZc5fkeepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdWkFmtZc:fkeep_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdWkFmtZc9fkeep_setC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01118WdWkFmtE4fstyC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3b2zC59OSSVerify5KrLib7Mh_01118WdWkFmtE;fmtE1F_walkC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2gec59OSSVerify5KrLib7Mh_00709WdWkFmtZb9outF_walkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8ltb_specC59OSSVerify5KrLib7Mh_01347WdGnumB;gnum_fstyleC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_NoneC59OSSVerify5KrLib7Mh_01118WdWkFmtE;fmtE1E_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdWkFmtZb9outE_walkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01347WdGnumB;gnum_estyleC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204C56Stdlib6ZArith6BinInt1Z;le_preorderC49OSSVerify5KrLib:WdVfDivtf39divtf3_vfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0066:WdVfAddtf39addtf3_vfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0066:WdVfMultf39multf3_vfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00669WdVfLetf28letf2_vfC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib7Mh_01348WdWkFmtF9img_bytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem<bytes_at_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00657WdWkProDfpclassifyl_walk_infC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00658WdVfSpec7vf_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00708WdWkFmtN5b_infC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00708WdWkFmtN5b_nanC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C49OSSVerify5KrLib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkDg@ztb_unsigned_addC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkDg9fin2_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkDg8rw2_loopC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05c59OSSVerify5KrLib7Mh_00706VdWkDg8rw2_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDg23dvkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkDg8rw1_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkDg:loop2_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDg29remuw_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDg37dg_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDg2:kloop_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00705VdWkG6g_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00705VdWkG:land_W_M32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDg37dg_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00705VdWkG=grisu_c2_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkGp8dn_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkGp8lpA_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkGp8lpB_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit6nth_exC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr4u8roC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp7digs_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp4isdgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp5isdgbC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7add_0_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr<nth_error_ltC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr:u8ro_frameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3zxbC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr9u8ro_readC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393MemAzext_extract_byteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp;isdgb_falseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp5dlt10C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge5zr_bvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp9digs_at_0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp9digs_at_SC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp:isdgb_trueC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison03c59OSSVerify5KrLib7Mh_00707WdStExp4dgt9C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3mrdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9alu_sltiuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp9neg_landWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp5se_lxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses:impl_morphC79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr>u8ro_transportC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp:isdgb_specC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp=digs_at_shiftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp5se_lyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp5se_lzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp9sgn_ltu_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStExp9sgn_ltu_aC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;v_sltiu_b2zC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC49OSSVerify5KrLib8PropExec5v_xorC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_mulwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit3w32C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge5inr64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u32arr_readC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr?u32arr_store_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6w_addwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_xorC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr<u32arr_writeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z<lor_eq_0_iffC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP=Z_lor_lt_pow2C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6w_mulwC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge:zr_mod_anyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00708WdStKit2=subw_rem_sx32C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge7zr_wordC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_divC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lxor_0_rC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge7zr_lxorC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00708WdStKit2:divuw_sx32C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop06c59OSSVerify5KrLib7Mh_00706WdStAl7al_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706WdStAl7al_stepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit7w32_updC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit=unsigned_sx32C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7nan_boxC46Stdlib5Lists4List2InC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge9zr_land_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag3fklC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0066?WdVfExtendsftf2>extendsftf2_vfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit8evt_frm0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag7fkl_setC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl9blk_b6a90C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrc59OSSVerify5KrLib7Mh_00709WdVfFmodl9body_postC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr6fmvdir02K4ELinuxProcessSemantics5Riscv5Instr4ffmt01c59OSSVerify5KrLib7Mh_00707WdStKit7fcs_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?mul_mod_distr_lc59OSSVerify5KrLib7Mh_00709WdVfFmodl8fm_post1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_commC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge9zr_shiftrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_addc59OSSVerify5KrLib7Mh_00709WdVfFmodl9blk_b6c30C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_opp_rC59OSSVerify5KrLib7Mh_00597WdWkMem=ztb_landW_addC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula09c59OSSVerify5KrLib7Mh_00709WdVfFmodl<unsigned_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl7shr_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl:land15_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl9landW_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0066=WdVfFloatsitf<floatsitf_vfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0066?WdVfFpclassifyl>fpclassifyl_vfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl9blk_b6a70C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl7fm_headC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl9blk_b6b40C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag8vff_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag8fkl_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl9blk_b6a40C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag8vff_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0066?WdVfExtenddftf2>extenddftf2_vfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070;WdVfScalbnl9body_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070;WdVfScalbnl9blk_b6dfcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070;WdVfScalbnl9blk_b6df8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070;WdVfScalbnl9blk_b6dbcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070;WdVfScalbnl9blk_b6d60C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem4zx32C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem@zext_extract_le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00658WdWkFmtB4keepC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses<eq_Reflexivec59OSSVerify5KrLib7Mh_00707WdStKit7xor_lt1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit7xor_gt0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit;land_W_2047C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00658WdWkFmtB<div1e9_magicC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00658WdWkFmtB8zx32_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706WdStUp<up_pass_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit9mod_diff0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706WdStUp7up_stepC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib6ZArith6BinInt1Z8sub_diagC56Stdlib6ZArith6BinInt1Z7mod_0_lc59OSSVerify5KrLib7Mh_00707WdStKit>land_pred_2047C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit=mod_pred_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof04c59OSSVerify5KrLib7Mh_00706WdStUp;up_inv_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit9land_2047C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706WdStUp7up_passC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit7le4_anyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706WdStUp<up_exit_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706WdStUp8up_roundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC49OSSVerify5KrLib8PropExec6v_sraiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_sraiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_xoriC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070>WdVfTrunctfdf29blk_b71acC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070>WdVfTrunctfdf29blk_b7114C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070>WdVfTrunctfdf29body_postC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop08".
Module VdWkDgC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import VdMath.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VdWkDgC () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbK47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions;bv_unsignedC79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C49OSSVerify5KrLib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC49OSSVerify5KrLib8PropExec9alu_sltiuC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C49OSSVerify5KrLib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorK4ELinuxProcessSemantics5Riscv5Instr5instr03C56Stdlib6ZArith6BinInt1Z4lxorC49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_xoriC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_lorC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;v_sltiu_b2zC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_subC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop05C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5instr0BC56Stdlib6ZArith6BinInt1Z3mulC49OSSVerify5KrLib8PropExec5v_mulC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5m_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divK4ELinuxProcessSemantics5Riscv5Instr5mulop01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC46Stdlib6ZArith4ZdivBZminus_mod_idemp_rK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib5Lists4List9nth_errorc59OSSVerify5KrLib7Mh_00707VdWkDgC4dclsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Nat2Z6inj_leC79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr3updC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphK46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC47Corelib4Init9Datatypes6lengthc59OSSVerify5KrLib7Mh_00707VdWkDgC8dcls_updC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDgC9dcls_lastC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:munch_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:wmono_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_boundC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib5Lists4List>nth_error_SomeC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic5proj1c59OSSVerify5KrLib7Mh_00707VdWkDgC8dec_byteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDgC=dcls_set_lastC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem2waC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr:u8arr_readC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr>u8arr_store_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3zxbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC79OSSVerify5KrLib2CJ3Lib7Mh_00393MemAzext_extract_byteC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_1'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses8or_morphC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6insideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDgC9fin1_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr:upd_lengthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib4Bool4Bool=negb_true_iffC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge8bv_ltu_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib6VdMath3VDM8land_W64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDgC<sub_mod_stepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr5u8arrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5wmonoC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv3Sem4core01C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succI4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z6shiftlK47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDgC@ztb_unsigned_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC56Stdlib6ZArith6BinInt1Z3oppc59OSSVerify5KrLib7Mh_00707VdWkDgC5tk_nzC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem4sx32C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells6cbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le4C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells7cell_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells5csizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_sllC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_sllC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem:length_le4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_frameC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib7Mh_00597WdWkMem8sx32_ztbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDgCAztb_unsigned_add2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkDgC8rw1_loopC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame7outsideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6sub_fpC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame<munch_weakenC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib7SFModel<mod64_land63C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5aluop03c59OSSVerify5KrLib7Mh_00707VdWkDgC9fin2_walkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c59OSSVerify5KrLib7Mh_00707VdWkDgC8rw2_loopC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Ltac fix_sbw :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?c)) _) => change (Z_to_le_bytes 1 c) with [Z_to_bv 8 c]
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => change (le1 w) with [Z_to_bv 8 (bv_unsigned w)]
  end.
Ltac show_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => idtac "mem=" m end.
Ltac brs := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let B := fresh "B" in destruct c eqn:B end.

(* [comment removed for export] *)
Lemma fin1_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => exists (res : Z) a1' a2' a3' a4' a5',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0x3e290) fc None m (seg_rom rsegs) /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e210) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_001 ())). Qed.

Lemma fin2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => exists (res : Z) a1' a2' a3' a4' a5',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0x3e290) fc None m (seg_rom rsegs) /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e248) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_002 ())). Qed.

Open Scope Z_scope.
Lemma sub_mod_step D r tk : 0 <= D < 2 ^ 64 -> 0 <= r < 2 ^ 64 -> 1 <= tk <= (D - r) mod 2 ^ 64 ->
  (D - (r + tk) mod 2 ^ 64) mod 2 ^ 64 = (D - r) mod 2 ^ 64 - tk.
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_003 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Definition dcls (bs : list byte) (n : nat) : Prop := forall j, (j < n)%nat -> exists b, nth_error bs j = Some b /\ (46 <= bv_unsigned b <= 57)%Z.
Lemma dcls_nil bs : dcls bs 0.
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_004 ())). Qed.
Lemma dcls_mono bs n n' : dcls bs n -> (n' <= n)%nat -> dcls bs n'.
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_005 ())). Qed.
Lemma dcls_upd bs n i b : dcls bs n -> (n <= i)%nat -> dcls (upd bs i b) n.
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_006 ())). Qed.
Lemma dcls_last bs len b : dcls bs (Z.to_nat (len - 1)) -> (1 <= len)%Z -> nth_error bs (Z.to_nat (len - 1)) = Some b -> (46 <= bv_unsigned b <= 57)%Z -> dcls bs (Z.to_nat len).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_007 ())). Qed.
Lemma dcls_set_last bs len b : dcls bs (Z.to_nat (len - 1)) -> (1 <= len)%Z -> (Z.to_nat (len - 1) < length bs)%nat -> (46 <= bv_unsigned b <= 57)%Z ->
  dcls (upd bs (Z.to_nat (len - 1)) b) (Z.to_nat len).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_008 ())). Qed.
Lemma dec_byte (b : byte) : (1 <= bv_unsigned b)%Z -> bv_unsigned (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b + -1)))) = (bv_unsigned b - 1)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_009 ())). Qed.

(* [comment removed for export] *)
Lemma rw1_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) < 2 ^ 63)%Z ->
  ((bv_unsigned a0 - bv_unsigned t5) mod 2 ^ 64 <= Z.of_nat n)%Z ->
  (1 <= bv_unsigned a4 <= (bv_unsigned a0 - bv_unsigned t5) mod 2 ^ 64)%Z ->
  a6 = Z_to_bv 64 (buf + len) ->
  dcls bs (Z.to_nat (len - 1)) ->
  (exists b, nth_error bs (Z.to_nat (len - 1)) = Some b /\ (bv_unsigned b <= 57)%Z /\
     (forall k, (0 <= k)%Z -> (k * bv_unsigned a4 <= (bv_unsigned a0 - bv_unsigned t5) mod 2 ^ 64)%Z -> (46 <= bv_unsigned b - k)%Z)) ->
  evt rsegs (fun ms' => exists (res : Z) t0' a1' a2' a3' a4' a5' a7' t5' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5' t6) F
               (Z_to_bv 64 0x3e290) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z /\ dcls bs' (Z.to_nat len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e0ec) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_010 ())). Qed.

Open Scope Z_scope.
Lemma tk_nz dv sh : dv = 100 \/ dv = 10 \/ dv = 1 -> 56 <= sh <= 59 -> 1 <= bv_unsigned (Z_to_bv 64 (Z.shiftl dv (Z.land sh 63))).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_011 ())). Qed.
Lemma ztb_unsigned_add k d : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 k) + d) = Z_to_bv 64 (k + d).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_012 ())). Qed.
Lemma ztb_unsigned_add2 k d e : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 k) + d + e) = Z_to_bv 64 (k + d + e).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_013 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma rw1_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 kap dv sh : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) < 2 ^ 63)%Z -> (Z.of_nat (length bs) < 2 ^ 31)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + Z.of_nat (length bs) <= kp)%Z -> (lenp + 4 <= buf \/ buf + Z.of_nat (length bs) <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (0 <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (0 <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z ->
  (bv_unsigned t5 < bv_unsigned a0)%Z -> (56 <= sh <= 59)%Z -> (dv = 100 \/ dv = 10 \/ dv = 1)%Z -> (1 <= kap <= 3)%Z -> (- 2 ^ 20 <= k0 <= 2 ^ 20)%Z ->
  t0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> t6 = Z_to_bv 64 dv -> a5 = Z_to_bv 64 sh -> t3 = Z_to_bv 64 kap ->
  dcls bs (Z.to_nat (len - 1)) ->
  (exists b, nth_error bs (Z.to_nat (len - 1)) = Some b /\ (bv_unsigned b <= 57)%Z /\
     (forall k, (0 <= k)%Z -> (k * bv_unsigned (Z_to_bv 64 (Z.shiftl dv (Z.land sh 63))) <= (bv_unsigned a0 - bv_unsigned t5) mod 2 ^ 64)%Z -> (46 <= bv_unsigned b - k)%Z)) ->
  evt rsegs (fun ms' => exists (res : Z) t0' t1' a1' a2' a3' a4' a5' a6' a7' t5' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5' t6) F
               (Z_to_bv 64 0x3e290) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs)); (kp, kp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + (kap - 1)))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)]
      /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z /\ dcls bs' (Z.to_nat len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e0bc) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_014 ())). Qed.

(* [comment removed for export] *)
Lemma rw2_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) < 2 ^ 63)%Z ->
  (bv_unsigned t4 < Z.of_nat n)%Z -> (1 <= bv_unsigned a1)%Z ->
  a6 = Z_to_bv 64 (buf + len) ->
  dcls bs (Z.to_nat (len - 1)) ->
  (exists b, nth_error bs (Z.to_nat (len - 1)) = Some b /\ (46 <= bv_unsigned b <= 57)%Z /\
     (forall k, (1 <= k)%Z -> ((k - 1) * bv_unsigned a1 <= bv_unsigned t4)%Z -> (46 <= bv_unsigned b - k)%Z)) ->
  evt rsegs (fun ms' => exists (res : Z) t0' a1' a2' a3' a4' a5' a7' t3' t4' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6) F
               (Z_to_bv 64 0x3e290) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z /\ dcls bs' (Z.to_nat len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e1cc) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_015 ())). Qed.

(* [comment removed for export] *)
Lemma rw2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 kap : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) < 2 ^ 63)%Z -> (Z.of_nat (length bs) < 2 ^ 31)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + Z.of_nat (length bs) <= kp)%Z -> (lenp + 4 <= buf \/ buf + Z.of_nat (length bs) <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (0 <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (0 <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z ->
  (1 <= bv_unsigned a1)%Z -> (- 2 ^ 20 <= kap <= 2 ^ 20)%Z -> (- 2 ^ 20 <= k0 <= 2 ^ 20)%Z ->
  t0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> t4 = Z_to_bv 64 kap ->
  (bv_unsigned a4 < bv_unsigned a0)%Z -> (bv_unsigned t3 * 10 = bv_unsigned a0)%Z -> (bv_unsigned a1 + bv_unsigned a0 < 2 ^ 64)%Z ->
  dcls bs (Z.to_nat (len - 1)) ->
  (exists b, nth_error bs (Z.to_nat (len - 1)) = Some b /\ (bv_unsigned b <= 57)%Z /\
     (forall k, (0 <= k)%Z -> (k * bv_unsigned a1 <= bv_unsigned a0 - bv_unsigned a4)%Z -> (46 <= bv_unsigned b - k)%Z)) ->
  evt rsegs (fun ms' => exists (res : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6) F
               (Z_to_bv 64 0x3e290) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs)); (kp, kp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + kap))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)]
      /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z /\ dcls bs' (Z.to_nat len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e178) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDgC ()) [] (Mh_0070_blobs1.kr_b_016 ())). Qed.

(* [comment removed for export] *)
Lemma loop2_walk : forall (k n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 sh Dl p2 : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (0 <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (0 <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (0 <= buf)%Z ->
  (n + k = 18)%nat -> (10 ^ Z.of_nat n <= Dl)%Z -> (Dl <= p2 < 2 ^ sh)%Z -> (56 <= sh <= 59)%Z -> (1 <= len <= 3 + Z.of_nat n)%Z -> (- 2 ^ 19 <= k0 <= 2 ^ 19)%Z ->
  t0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> t4 = Z_to_bv 64 (- Z.of_nat n) -> a5 = Z_to_bv 64 sh -> t5 = Z_to_bv 64 10 ->
  a0 = Z_to_bv 64 Dl -> a4 = Z_to_bv 64 p2 -> t2 = Z_to_bv 64 (2 ^ sh - 1) -> a1 = Z_to_bv 64 (2 ^ sh) ->
  dcls bs (Z.to_nat len) ->
  evt rsegs (fun ms' => exists (res len' dk : Z) t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t6' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6') F
               (Z_to_bv 64 0x3e290) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + dk))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-18 <= dk <= 2)%Z /\ dcls bs' (Z.to_nat len'))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e130) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_017 ())). Qed.


End VdWkDgC.
Module VdWkDg2C.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDgC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VdWkDg2C () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3eqbC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib7Mh_00597WdWkKit=swrap32_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_remuwC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_posC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC49OSSVerify5KrLib8PropExec7v_divuwC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init5Logic4True01".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Ltac no_vars c := match c with context [?x] => is_var x; fail 2 "open term" | _ => idtac end.
Ltac cbr := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  no_vars c; let v := eval vm_compute in c in change c with v; cbv iota end.

Open Scope Z_scope.
Definition dvk (j : nat) : Z := match j with 3%nat => 100 | 2%nat => 10 | _ => 1 end.
Lemma remuw_val (wx : word) (d : Z) : bv_unsigned wx < 2 ^ 31 -> 0 < d < 2 ^ 31 -> v_remuw wx (Z_to_bv 64 d) = Z_to_bv 64 (bv_unsigned wx mod d).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDg2C ()) [] (Mh_0070_blobs1.kr_b_018 ())). Qed.
Lemma divuw_val (wx : word) (d : Z) : bv_unsigned wx < 2 ^ 31 -> 0 < d < 2 ^ 31 -> v_divuw wx (Z_to_bv 64 d) = Z_to_bv 64 (bv_unsigned wx / d).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDg2C ()) [] (Mh_0070_blobs1.kr_b_019 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma kloop_walk : forall (j : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 sh Dl p1 Wp1 : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (0 <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (0 <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (0 <= buf)%Z ->
  (1 <= j <= 3)%nat -> (56 <= sh <= 59)%Z -> (1 <= Dl <= Wp1)%Z -> (2 ^ sh <= Wp1 < 2 ^ 64)%Z -> (0 <= p1 < 10 * dvk j)%Z -> (0 <= len <= 3 - Z.of_nat j)%Z ->
  (len = 0 -> p1 = Wp1 / 2 ^ sh)%Z -> (- 2 ^ 19 <= k0 <= 2 ^ 19)%Z ->
  t0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> t4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 sh -> t5 = Z_to_bv 64 len ->
  a0 = Z_to_bv 64 Dl -> a4 = Z_to_bv 64 (Wp1 mod 2 ^ sh) -> t2 = Z_to_bv 64 (2 ^ sh - 1) -> a1 = Z_to_bv 64 (2 ^ sh) ->
  s0 = Z_to_bv 64 p1 -> t6 = Z_to_bv 64 (dvk j) -> t3 = Z_to_bv 64 (Z.of_nat j) -> s1 = Z_to_bv 64 0xcccccccd00000000 ->
  (Dl <= p1 * 2 ^ sh + Wp1 mod 2 ^ sh <= Wp1)%Z ->
  dcls bs (Z.to_nat len) ->
  evt rsegs (fun ms' => exists (res len' dk : Z) t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (Z_to_bv 64 0x3e290) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + dk))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-18 <= dk <= 2)%Z /\ dcls bs' (Z.to_nat len'))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e06c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_020 ())). Qed.

End VdWkDg2C.
Module VdWkDg3C.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDgC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg2C.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Ltac setreg_by n e t := let v := getreg n in replace v with e by t.

(* [comment removed for export] *)
Definition dg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo buf kp lenp k0 : Z) : machine_state -> Prop :=
  fun ms' => exists (res len' dk : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (bv_unsigned sp) [C8 (Z_to_bv 64 kp)] /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + dk))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-18 <= dk <= 2)%Z /\ dcls bs' (Z.to_nat len').

Lemma dg_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp k0 Wm W Wp E e1 e3 e5 : Z) (bs lb : list byte),
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 kp)] ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp + 8 <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp + 8 <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp + 8 <= buf)%Z ->
  (1 <= Wm <= Wp)%Z -> (W <= Wp)%Z -> (0 <= W)%Z -> (2 ^ 59 <= Wp <= 2 ^ 64 - 2)%Z -> (-59 <= E <= -56)%Z -> (- 2 ^ 19 <= k0 <= 2 ^ 19)%Z ->
  (0 <= e1 < 2 ^ 64)%Z -> (0 <= e3 < 2 ^ 64)%Z -> (0 <= e5 < 2 ^ 64)%Z -> bv_swrap 32 e1 = E -> bv_swrap 32 e3 = E -> bv_swrap 32 e5 = E ->
  a0 = Z_to_bv 64 Wm -> a1 = Z_to_bv 64 e1 -> a2 = Z_to_bv 64 W -> a3 = Z_to_bv 64 e3 -> a4 = Z_to_bv 64 Wp -> a5 = Z_to_bv 64 e5 ->
  a6 = Z_to_bv 64 buf -> a7 = Z_to_bv 64 lenp ->
  evt rsegs (dg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo buf kp lenp k0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3dfe0) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_021 ())). Qed.

End VdWkDg3C.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath VdTab.
Module VdWkGC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath VdTab. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdTab OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDgC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg2C OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg3C.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VdWkGC () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC56Stdlib6ZArith6BinInt1Z4onesK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z9land_onesC59OSSVerify5KrLib6VdMath3VDM8land_W64C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Open Scope Z_scope.
Lemma land_W_M32 x : Z.land (Z.land x 18446744073709551615) 4294967295 = x mod 2 ^ 32.
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkGC ()) [] (Mh_0070_blobs1.kr_b_022 ())). Qed.
Close Scope Z_scope.

Ltac setreg2 n e t := let v := getreg n in replace v with e by (symmetry; t).

(* [comment removed for export] *)
Definition g_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : word -> option byte)
    (lo buf kp lenp : Z) : machine_state -> Prop :=
  fun ms' => exists (res len' kz : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F'
               (ret_pc ra) fc' None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 kz)] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-343 <= kz <= 309)%Z /\ frm0 fc' /\ dcls bs' (Z.to_nat len').

(* [comment removed for export] *)
Lemma grisu_c2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (spz lo buf kp lenp mi mie pe P Wn sh : Z) (junk16 bs kb lb : list byte) (o_ra o_s0 o_s1 o_s2 o_s3 o_s4 o_s5 o_s6 : word),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo spz -> (lo + 48 <= spz)%Z -> (spz + 80 < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z -> (bv_unsigned o_ra mod 2 = 0)%Z ->
  rw_cells rsegs m spz [CB 16 junk16; C8 o_s6; C8 o_s5; C8 o_s4; C8 o_s3; C8 o_s2; C8 o_s1; C8 o_s0; C8 o_ra] ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (spz + 80 <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (spz + 80 <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (spz + 80 <= buf)%Z ->
  (1 <= mi)%Z -> (sh = mie - pe + 10)%Z -> (9 <= sh <= 62)%Z -> (mi * 2 ^ sh <= Wn * 2 ^ 11)%Z -> (Wn * 2 ^ 11 <= P * 2 ^ 10)%Z -> (2 ^ 63 <= P * 2 ^ 10 < 2 ^ 64)%Z ->
  (-1021 <= -50 - pe <= 1077)%Z -> (-2000 <= mie <= 2000)%Z -> (0 <= Wn)%Z -> (0 <= P)%Z ->
  a0 = Z_to_bv 64 (pe + 1) -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 kp -> a4 = Z_to_bv 64 mie -> a5 = Z_to_bv 64 pe -> a6 = Z_to_bv 64 Wn -> a7 = Z_to_bv 64 mi ->
  t1 = Z_to_bv 64 P -> t4 = Z_to_bv 64 18446744073709551615 -> s0 = Z_to_bv 64 buf -> s1 = Z_to_bv 64 lenp -> sp = Z_to_bv 64 spz ->
  evt rsegs (g_post o_ra (Z_to_bv 64 (spz + 80)) gp tp o_s0 o_s1 o_s2 o_s3 o_s4 o_s5 o_s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3daf4) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_023 ())). Qed.

End VdWkGC.
Module VdWkGpC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath VdTab. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdTab OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDgC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg2C OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg3C OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkGC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VdWkGpC () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z:pow_succ_rK4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec7alu_andC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09I4ELinuxProcessSemantics5Riscv7Prelude4tree00C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC49OSSVerify5KrLib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr08K47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib6VdMath3VDM<land_pow2_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2ex01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01C59OSSVerify5KrLib6VdMath3VDM<land_pow2_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz01I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega6VarMap1t03C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge=bv_lts_zero_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtK4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C56Stdlib6ZArith6BinInt1Z9log2_specC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rK46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05C56Stdlib6ZArith4Znat5Z2Nat2idC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP4frm0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics5Riscv3Sem7reg_getC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr5u8arrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkGC6g_postC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc59OSSVerify5KrLib7Mh_00707VdWkGpC<grisu_d_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707VdWkGpC<grisu_n_walkC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

(* [comment removed for export] *)
Lemma lpA_walk : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (X e : Z),
  (1 <= n)%nat -> (2 ^ 53 <= X * 2 ^ Z.of_nat n < 2 ^ 54)%Z -> (0 <= X)%Z ->
  a1 = Z_to_bv 64 4503599627370496 -> t1 = Z_to_bv 64 X -> a5 = Z_to_bv 64 e ->
  evt rsegs (fun ms' => exists a0',
      ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (X * 2 ^ Z.of_nat n)) t2 s0 s1 a0' a1 a2 a3 a4 (Z_to_bv 64 (e - Z.of_nat n)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0x3dab8) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3daa8) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkGpC ()) [] (Mh_0070_blobs1.kr_b_024 ())). Qed.

(* [comment removed for export] *)
Lemma lpB_walk : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (Y e : Z),
  (1 <= n)%nat -> (2 ^ 52 <= Y * 2 ^ Z.of_nat n < 2 ^ 53)%Z -> (0 <= Y)%Z ->
  a6 = Z_to_bv 64 Y -> a0 = Z_to_bv 64 e ->
  evt rsegs (fun ms' => exists a1',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (e - Z.of_nat n)) a1' a2 a3 a4 a5 (Z_to_bv 64 (Y * 2 ^ Z.of_nat n)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0x3dacc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3dabc) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkGpC ()) [] (Mh_0070_blobs1.kr_b_025 ())). Qed.


(* [comment removed for export] *)
Lemma grisu_n_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp u : Z) (bs kb lb : list byte),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo (bv_unsigned sp) -> (lo + 128 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (forall r, bv_unsigned r = 10%Z -> reg_get F r = Z_to_bv 64 u) -> (2 ^ 52 <= u < 2 ^ 63)%Z ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp <= buf)%Z ->
  a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 lenp -> a2 = Z_to_bv 64 kp ->
  evt rsegs (g_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3da20) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_026 ())). Qed.

Open Scope Z_scope.
Lemma dn_facts f : 1 <= f < 2 ^ 52 -> exists n : nat, (1 <= n <= 52)%nat /\ 2 ^ 52 <= f * 2 ^ Z.of_nat n < 2 ^ 53 /\ 2 ^ 53 <= (2 * f + 1) * 2 ^ Z.of_nat n < 2 ^ 54.
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkGpC ()) [] (Mh_0070_blobs1.kr_b_027 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma grisu_d_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp u : Z) (bs kb lb : list byte),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo (bv_unsigned sp) -> (lo + 128 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (forall r, bv_unsigned r = 10%Z -> reg_get F r = Z_to_bv 64 u) -> (1 <= u < 2 ^ 52)%Z ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp <= buf)%Z ->
  a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 lenp -> a2 = Z_to_bv 64 kp ->
  evt rsegs (g_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3da20) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_028 ())). Qed.

(* [comment removed for export] *)
Theorem grisu3_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp u : Z) (bs kb lb : list byte),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo (bv_unsigned sp) -> (lo + 128 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (forall r, bv_unsigned r = 10%Z -> reg_get F r = Z_to_bv 64 u) -> (1 <= u < 2 ^ 63)%Z ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp <= buf)%Z ->
  a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 lenp -> a2 = Z_to_bv 64 kp ->
  evt rsegs (g_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3da20) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkGpC ()) [] (Mh_0070_blobs1.kr_b_029 ())). Qed.

End VdWkGpC.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdWkFmtU. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.
Module WdWkFmtI.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdWkFmtU. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkFmtB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkFmtD OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111.WdWkFmtE OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdWkFmtU OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111.WdWkOut.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtZ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtUf OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtUe OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtH.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

(* [comment removed for export] *)
Lemma estyle_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo B ia iz n p2 fa B0 cap k lbf : Z) (ne : nat) (ibuf jB dbuf ebp eb : list byte) (ws : list word) (w0 : word) (c6 c7 G : word)
   (rpos rend wbase wfn bufp bsz mode lockv cookie : word) (J : fjunk),
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> (lo + 304 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= bv_unsigned s0 - 1056)%Z ->
  (bv_unsigned s0 < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z ->
  ro_cells rsegs m 0xc5ab8 [C8 (Z_to_bv 64 0xf8ac0)] -> ro_cells rsegs m 0xf8ac0 [C8 G] ->
  u32arr rsegs m B ws -> (bv_unsigned sp <= B)%Z -> (B + 4 * Z.of_nat (length ws) <= bv_unsigned s0 - 544)%Z -> (B + 4 * Z.of_nat (length ws) < 2 ^ 63)%Z ->
  (0 <= ia < iz)%Z -> (iz <= Z.of_nat (length ws))%Z -> limbs_ok ws ia iz -> nth_error ws (Z.to_nat ia) = Some w0 ->
  (0 <= p2 <= 20)%Z -> (p2 <= Z.max 1 (ndig (bv_unsigned w0)) - 1 + 9 * (iz - ia - 1))%Z -> (4 <= ne <= 6)%nat ->
  rw_cells rsegs m (bv_unsigned s0 + -496) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (bv_unsigned s0 - 405 - Z.of_nat ne)); CB 8 jB; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xf8ac0);
                                             C8 (Z_to_bv 64 0); C8 c6; C8 c7; C8 (Z_to_bv 64 fa)] ->
  rw_cells rsegs m (bv_unsigned s0 + -417) [CB (12 - ne) ebp; CB ne eb] -> rw_cells rsegs m (bv_unsigned s0 + -405) [CB 9 dbuf] ->
  fst_at m fa B0 cap k lbf ibuf rpos rend wbase wfn bufp bsz mode lockv cookie J -> fgeo (bv_unsigned s0) fa B0 cap -> (k + 40 <= cap)%Z ->
  s1 = Z_to_bv 64 (B + 4 * ia) -> s2 = Z_to_bv 64 p2 -> s7 = Z_to_bv 64 (B + 4 * iz) -> s8 = Z_to_bv 64 69 ->
  s10 = Z_to_bv 64 n -> s11 = Z_to_bv 64 p2 ->
  evt rsegs (fun ms' => exists (d0 : byte) (ds : list byte) ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' m',
      isdigb d0 /\ Forall isdigb ds /\ Z.of_nat (length ds) = p2 /\
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' (Z_to_bv 64 1) s6' s7' s8' s9' s10' s11' t3' t4' t5' t6') F
               (Z_to_bv 64 0xb186c) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (B0 + k, B0 + k + 40); (fa + 40, fa + 48); (bv_unsigned s0 + -480, bv_unsigned s0 + -472);
                (bv_unsigned s0 + -440, bv_unsigned s0 + -432); (bv_unsigned s0 + -405, bv_unsigned s0 + -396)]%Z m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' (bv_unsigned s0 + -496) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (bv_unsigned s0 - 405 - Z.of_nat ne)); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xf8ac0);
                                             C8 (Z_to_bv 64 0); C8 c6; C8 (Z_to_bv 64 69319); C8 (Z_to_bv 64 fa)]
      /\ fst_at m' fa B0 cap (k + Z.of_nat (length (eout d0 ds p2 ++ eb))) lbf (upd_bytes ibuf (Z.to_nat k) (eout d0 ds p2 ++ eb)) rpos rend wbase wfn bufp bsz mode lockv cookie J)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xb1490) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_030 ())). Qed.

End WdWkFmtI.
Module WdWkFmtZb.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdWkFmtU. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111.WdWkOut OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkFmtB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkFmtD OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111.WdWkFmtE OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdWkFmtU OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtZ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtH OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdWkFmtI.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Lemma outF_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo B ia ir iz n p2 pl fa B0 cap k lbf : Z) (ibuf jB dbuf : list byte) (ws : list word) (w0 : word) (estr ns G : word)
   (ora os0 os1 os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 : word)
   (rpos rend wbase wfn bufp bsz mode lockv cookie : word) (J : fjunk),
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> (lo + 304 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= bv_unsigned s0 - 1056)%Z ->
  (1024 <= bv_unsigned s0 < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z ->
  ro_cells rsegs m 0xc5ab8 [C8 (Z_to_bv 64 0xf8ac0)] -> ro_cells rsegs m 0xf8ac0 [C8 G] ->
  u32arr rsegs m B ws -> (bv_unsigned sp <= B)%Z -> (B + 4 * Z.of_nat (length ws) <= bv_unsigned s0 - 544)%Z ->
  (0 <= ia)%Z -> (0 <= ir)%Z -> (ir < Z.of_nat (length ws))%Z -> (iz <= Z.of_nat (length ws))%Z -> (ir - 1 <= ia <= ir + 1)%Z ->
  (forall i x, (Z.min ia ir <= i <= ir)%Z -> nth_error ws (Z.to_nat i) = Some x -> (bv_unsigned x < 1000000000)%Z) ->
  limbs_ok ws (ir + 1) iz -> nth_error ws (Z.to_nat (Z.min ia ir)) = Some w0 -> (ir < ia -> bv_unsigned w0 = 0)%Z ->
  (0 <= p2 <= 20)%Z -> (p2 <= Z.max 0 (9 * (iz - ir - 1)))%Z -> (0 <= pl <= 1)%Z -> (1 <= n < 2 ^ 31)%Z ->
  rw_cells rsegs m (bv_unsigned s0 + -496) [C8 (Z_to_bv 64 1); C8 estr; CB 8 jB; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xf8ac0); C8 ns; C8 (Z_to_bv 64 (68534 - pl));
                                             C8 (Z_to_bv 64 pl); C8 (Z_to_bv 64 fa)] ->
  rw_cells rsegs m (bv_unsigned s0 + -405) [CB 9 dbuf] ->
  rw_cells rsegs m (bv_unsigned s0 + -112) [C8 G; C8 os11; C8 os10; C8 os9; C8 os8; C8 os7; C8 os6; C8 os5; C8 os4; C8 os3; C8 os2; C8 os1; C8 os0; C8 ora] ->
  fst_at m fa B0 cap k lbf ibuf rpos rend wbase wfn bufp bsz mode lockv cookie J -> fgeo (bv_unsigned s0) fa B0 cap -> (k + 41 <= cap)%Z ->
  s1 = Z_to_bv 64 (B + 4 * ia) -> s2 = Z_to_bv 64 p2 -> s5 = Z_to_bv 64 pl -> s6 = Z_to_bv 64 (B + 4 * ir) -> s7 = Z_to_bv 64 (B + 4 * iz) -> s8 = Z_to_bv 64 70 ->
  s9 = Z_to_bv 64 p2 -> s10 = Z_to_bv 64 n -> s11 = Z_to_bv 64 p2 ->
  evt rsegs (fun ms' => exists (d1 d2 : list byte) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      Forall isdigb d1 /\ Forall isdigb d2 /\
      Z.of_nat (length d1) = ((if (ia <=? ir)%Z then Z.max 1 (ndig (bv_unsigned w0)) else 1) + 9 * (ir - Z.min ia ir))%Z /\ Z.of_nat (length d2) = p2 /\
      ms' = MS (mkR ora s0 gp tp t0' t1' t2' os0 os1 (Z_to_bv 64 n) a1' a2' a3' a4' a5' a6' a7' os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 t3' t4' t5' t6') F
               (ret_pc ora) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned s0); (B0 + k, B0 + k + 41); (fa + 40, fa + 48)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ fst_at m' fa B0 cap (k + Z.of_nat (length (pfxb pl ++ d1 ++ (if (0 <? p2)%Z then Z_to_bv 8 46 :: d2 else [])))) lbf
                (upd_bytes ibuf (Z.to_nat k) (pfxb pl ++ d1 ++ (if (0 <? p2)%Z then Z_to_bv 8 46 :: d2 else []))) rpos rend wbase wfn bufp bsz mode lockv cookie J)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xb13d8) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_031 ())). Qed.

Lemma outE_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo B ia iz n p2 pl fa B0 cap k lbf : Z) (ne : nat) (ibuf jB dbuf ebp eb : list byte) (ws : list word) (w0 : word) (G : word)
   (ora os0 os1 os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 : word)
   (rpos rend wbase wfn bufp bsz mode lockv cookie : word) (J : fjunk),
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> (lo + 304 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= bv_unsigned s0 - 1056)%Z ->
  (1024 <= bv_unsigned s0 < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z ->
  ro_cells rsegs m 0xc5ab8 [C8 (Z_to_bv 64 0xf8ac0)] -> ro_cells rsegs m 0xf8ac0 [C8 G] ->
  u32arr rsegs m B ws -> (bv_unsigned sp <= B)%Z -> (B + 4 * Z.of_nat (length ws) <= bv_unsigned s0 - 544)%Z ->
  (0 <= ia < iz)%Z -> (iz <= Z.of_nat (length ws))%Z -> limbs_ok ws ia iz -> nth_error ws (Z.to_nat ia) = Some w0 ->
  (0 <= p2 <= 20)%Z -> (p2 <= Z.max 1 (ndig (bv_unsigned w0)) - 1 + 9 * (iz - ia - 1))%Z -> (4 <= ne <= 6)%nat -> length eb = ne ->
  (0 <= pl <= 1)%Z -> (1 <= n < 2 ^ 31)%Z ->
  rw_cells rsegs m (bv_unsigned s0 + -496) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (bv_unsigned s0 - 405 - Z.of_nat ne)); CB 8 jB; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xf8ac0);
                                             C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (68534 - pl)); C8 (Z_to_bv 64 pl); C8 (Z_to_bv 64 fa)] ->
  rw_cells rsegs m (bv_unsigned s0 + -417) [CB (12 - ne) ebp; CB ne eb] -> rw_cells rsegs m (bv_unsigned s0 + -405) [CB 9 dbuf] ->
  rw_cells rsegs m (bv_unsigned s0 + -112) [C8 G; C8 os11; C8 os10; C8 os9; C8 os8; C8 os7; C8 os6; C8 os5; C8 os4; C8 os3; C8 os2; C8 os1; C8 os0; C8 ora] ->
  fst_at m fa B0 cap k lbf ibuf rpos rend wbase wfn bufp bsz mode lockv cookie J -> fgeo (bv_unsigned s0) fa B0 cap -> (k + 41 <= cap)%Z ->
  s1 = Z_to_bv 64 (B + 4 * ia) -> s2 = Z_to_bv 64 p2 -> s5 = Z_to_bv 64 pl -> s7 = Z_to_bv 64 (B + 4 * iz) -> s8 = Z_to_bv 64 69 ->
  s10 = Z_to_bv 64 n -> s11 = Z_to_bv 64 p2 ->
  evt rsegs (fun ms' => exists (d0 : byte) (ds : list byte) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      isdigb d0 /\ Forall isdigb ds /\ Z.of_nat (length ds) = p2 /\
      ms' = MS (mkR ora s0 gp tp t0' t1' t2' os0 os1 (Z_to_bv 64 n) a1' a2' a3' a4' a5' a6' a7' os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 t3' t4' t5' t6') F
               (ret_pc ora) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned s0); (B0 + k, B0 + k + 41); (fa + 40, fa + 48)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ fst_at m' fa B0 cap (k + Z.of_nat (length (pfxb pl ++ eout d0 ds p2 ++ eb))) lbf
                (upd_bytes ibuf (Z.to_nat k) (pfxb pl ++ eout d0 ds p2 ++ eb)) rpos rend wbase wfn bufp bsz mode lockv cookie J)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xb13d8) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_032 ())). Qed.

End WdWkFmtZb.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdVfDivtf3.
Module WdWkFmtZc.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdWkFmtU. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdVfDivtf3. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.WdLibc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111.WdWkOut OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkFmtB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkFmtC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkFmtD OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkFmtR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111.WdWkFmtE OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdWkFmtU OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtH OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.WdGnum OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdGnumB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdVfSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfLetf2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfMultf3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfAddtf3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdVfDivtf3.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdWkFmtZb.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdWkFmtZc () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_getK47Corelib4Init5Logic2eq01c59OSSVerify5KrLib7Mh_00709WdWkFmtZc5fkeepC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01C47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics5Riscv7PreludeCbvmap_get_set_otherC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_set".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

(* [comment removed for export] *)
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac noimp := repeat match goal with H : ?A -> ?B |- _ => match type of A with Prop => clear H end end.
Ltac qlia := solve [ nodisj; noimp; lia ].
(* [comment removed for export] *)
Ltac hide_disj := repeat match goal with
  | H : ?A \/ ?B |- _ => change (keep (A \/ B)) in H
  | H : ?A -> ?B |- _ => match type of A with Prop => change (keep (A -> B)) in H end end.
Ltac show_disj := unfold keep in *.
Ltac qtransport m m' MU WM := hide_disj; transport_after_call rsegs m m' MU WM; show_disj.

(* [comment removed for export] *)
Definition fkeep (F F' : bvmap 5 word) : Prop := forall r : bv 5, r <> 10%bv -> bvmap_get r F' = bvmap_get r F.
Lemma fkeep_refl F : fkeep F F.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkFmtZc ()) [] (Mh_0070_blobs1.kr_b_033 ())). Qed.
Lemma fkeep_trans F1 F2 F3 : fkeep F1 F2 -> fkeep F2 F3 -> fkeep F1 F3.
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkFmtZc ()) [] (Mh_0070_blobs1.kr_b_034 ())). Qed.
Lemma fkeep_set F c : fkeep F (bvmap_set 10%bv c F).
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkFmtZc ()) [] (Mh_0070_blobs1.kr_b_035 ())). Qed.

(* [comment removed for export] *)
Definition fmtfp_ret (ora fp gp tp os0 os1 os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 : word) (F : bvmap 5 word) (lo : Z) (m : word -> option byte)
    (fa B0 cap k lbf : Z) (ibuf : list byte) (rpos rend wbase wfn bufp bsz mode lockv cookie : word) (J : fjunk) (P : list byte -> Prop) : machine_state -> Prop :=
  fun ms' => exists (bs : list byte) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m',
      P bs /\ (1 <= Z.of_nat (length bs) <= 26)%Z /\
      ms' = MS (mkR ora fp gp tp t0' t1' t2' os0 os1 (Z_to_bv 64 (Z.of_nat (length bs))) a1' a2' a3' a4' a5' a6' a7' os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 t3' t4' t5' t6') F'
               (ret_pc ora) fc' None m' (seg_rom rsegs)
      /\ fkeep F F'
      /\ munch [(lo, bv_unsigned fp); (B0 + k, B0 + k + 41); (fa + 40, fa + 48)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ fst_at m' fa B0 cap (k + Z.of_nat (length bs)) lbf (upd_bytes ibuf (Z.to_nat k) bs) rpos rend wbase wfn bufp bsz mode lockv cookie J.

Theorem fmtfp_fromD_walk : forall (ra gp tp t0 t1 t2 fp a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo ia iz ir p s fa B0 cap k lbf : Z) (ws : list word) (w0 : word) (j1 j2 j3 ibuf : list byte) (G : word)
   (ora os0 os1 os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 : word)
   (rpos rend wbase wfn bufp bsz mode lockv cookie : word) (J : fjunk),
  let B := (bv_unsigned fp + -1056)%Z in
  (0 <= ia < iz)%Z -> (iz <= 128)%Z -> length ws = 128%nat -> (ir = 0 \/ ir = 122)%Z -> (ir = 122 -> ia <= 122)%Z ->
  limbs_ok ws ia (Z.max iz (ir + 1)) -> (ir = 0%Z -> lowz ws ia) ->
  nth_error ws (Z.to_nat ia) = Some w0 -> bv_unsigned w0 <> 0%Z -> (ia = 0%Z -> bv_unsigned w0 < 999999999)%Z ->
  (p = 15 \/ p = 17)%Z -> (0 <= s <= 1)%Z ->
  mem_inv rsegs m -> stk rsegs m lo B -> (lo <= bv_unsigned fp - 4640)%Z -> (bv_unsigned fp < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z ->
  u32arr rsegs m B ws ->
  rw_cells rsegs m (bv_unsigned fp + -544)
         [C8 (Z_to_bv 64 0); CB 40 j1; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 103); CB 8 j2; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xf8ac0);
          C8 (Z_to_bv 64 (1 - s)); C8 (Z_to_bv 64 (68534 - s)); C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 fa); C4 (Z_to_bv 64 0); CB 308 j3;
          C8 G; C8 os11; C8 os10; C8 os9; C8 os8; C8 os7; C8 os6; C8 os5; C8 os4; C8 os3; C8 os2; C8 os1; C8 os0; C8 ora] ->
  ro_cells rsegs m 0xc5ab8 [C8 (Z_to_bv 64 0xf8ac0)] -> ro_cells rsegs m 0xf8ac0 [C8 G] ->
  fst_at m fa B0 cap k lbf ibuf rpos rend wbase wfn bufp bsz mode lockv cookie J -> fgeo (bv_unsigned fp) fa B0 cap -> (k + 41 <= cap)%Z ->
  evt rsegs (fmtfp_ret ora fp gp tp os0 os1 os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 F lo m fa B0 cap k lbf ibuf rpos rend wbase wfn bufp bsz mode lockv cookie J
               (fun bs => WDL.gnum (zs bs) = true))
    (MS (mkR ra (Z_to_bv 64 B) gp tp t0 t1 t2 fp (Z_to_bv 64 (B + 4 * ia)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 (Z_to_bv 64 103) s5 (Z_to_bv 64 (B + 4 * ir)) s7 s8 s9 s10 (Z_to_bv 64 (B + 4 * iz)) t3 t4 t5 t6) F
        (Z_to_bv 64 0xb0828) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_036 ())). Qed.

End WdWkFmtZc.
Module WdWkFmtN.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkPro OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111.WdWkOut OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdVfSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfLetf2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtF.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Definition b_inf : list byte := [Z_to_bv 8 105; Z_to_bv 8 110; Z_to_bv 8 102].
Definition b_nan : list byte := [Z_to_bv 8 110; Z_to_bv 8 97; Z_to_bv 8 110].

Lemma nonfin_walk : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo pl lq hq fa B0 cap k lbf : Z) (ibuf j1 j2 j3 : list byte) (c0 c456 G e2w : word)
   (ora os0 os1 os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 : word)
   (rpos rend wbase wfn bufp bsz mode lockv cookie : word) (J : fjunk),
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned s0 + -1056) -> (lo + 64 <= bv_unsigned s0 + -1056)%Z -> (bv_unsigned s0 < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z ->
  ro_cells rsegs m 0xf8ac0 [C8 G] ->
  (0 <= lq < 2 ^ 64)%Z -> (0 <= hq < 2 ^ 64)%Z -> ((hq mod 2 ^ 63) / 2 ^ 48 = 32767)%Z -> (0 <= pl <= 1)%Z ->
  rw_cells rsegs m (bv_unsigned s0 + -544) [C8 c0; CB 80 j1; C8 c456; C8 (Z_to_bv 64 (68534 - pl)); C8 (Z_to_bv 64 pl); CB 8 j2; C4 e2w; CB 308 j3;
          C8 G; C8 os11; C8 os10; C8 os9; C8 os8; C8 os7; C8 os6; C8 os5; C8 os4; C8 os3; C8 os2; C8 os1; C8 os0; C8 ora] ->
  fst_at m fa B0 cap k lbf ibuf rpos rend wbase wfn bufp bsz mode lockv cookie J -> fgeo (bv_unsigned s0) fa B0 cap -> (k + 4 <= cap)%Z ->
  evt rsegs (fun ms' => exists (sb : list byte) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' fc' m',
      (sb = b_inf \/ sb = b_nan) /\
      ms' = MS (mkR ora s0 gp tp t0' t1' t2' os0 os1 (Z_to_bv 64 (pl + 3)) a1' a2' a3' a4' a5' a6' a7' os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 t3' t4' t5' t6') F
               (ret_pc ora) fc' None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned s0); (B0 + k, B0 + k + 4); (fa + 40, fa + 48)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ fst_at m' fa B0 cap (k + pl + 3) lbf (upd_bytes ibuf (Z.to_nat k) (pfxb pl ++ sb)) rpos rend wbase wfn bufp bsz mode lockv cookie J)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned s0 + -1056)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 103) (Z_to_bv 64 0xf8ac0) s5 s6 (Z_to_bv 64 1)
             (Z_to_bv 64 hq) (Z_to_bv 64 lq) (Z_to_bv 64 fa) (Z_to_bv 64 0) t3 t4 t5 t6) F (Z_to_bv 64 0xb0358) fc None m (seg_rom rsegs)).
Proof.
Ltac nf_tail SBp SBi SBn s0 gp tp F lo fa B0 cap k pl lbf ibuf Sv sbv :=
    zrun0; cbr; zrun0; dbr; zrun0; cbr; zrun0_to 0xaeb70%Z;
    (lazymatch goal with |- evt _ _ (MS _ _ _ ?fcc _ ?mm _) =>
       callx (fwritex_walk _ _ gp tp _ _ _ s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fcc mm lo fa B0 cap k pl (68534 - pl)%Z lbf ibuf (pfxb pl)) (bv_unsigned s0 + -1056)%Z
         by (first [ eassumption | reflexivity | lia | (apply SBp; assumption) ]) end);
    unfold fileC in *; zrun0; cbr; zrun0_to 0xaeb70%Z; replace (B0 + k + pl)%Z with (B0 + (k + pl))%Z in * by lia;
    (lazymatch goal with |- evt _ _ (MS _ _ _ ?fcc _ ?mm _) =>
       callx (fwritex_walk _ _ gp tp _ _ _ s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fcc mm lo fa B0 cap (k + pl)%Z 3%Z Sv lbf (upd_bytes ibuf (Z.to_nat k) (pfxb pl)) sbv) (bv_unsigned s0 + -1056)%Z
         by (first [ eassumption | reflexivity | lia | (rewrite upd_bytes_length by lia; lia) | (apply SBi; assumption) | (apply SBn; assumption) ]) end);
    unfold fileC in *; zrun0; cbr; zrun0; dbr; zrun0; rewrite bv_eqb_refl; zrun0.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_037 ())). Qed.
End WdWkFmtN.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdWkFmtA.
Module WdWkFmtNA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdWkFmtA. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkPro OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111.WdWkOut OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdWkFmtA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0134.WdWkFmtF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdWkFmtN.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdWkFmtNA () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib7Mh_01348WdWkFmtF6fst_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01348WdWkFmtF4fgeo00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2or00C59OSSVerify5KrLib7Mh_01117WdWkOut5fileCC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC47Corelib4Init9Datatypes6lengthC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC49OSSVerify5KrLib8WdWkFmtA:fmtA1_postC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C49OSSVerify5KrLib8WdWkFmtA:fmtA1_walkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameBro_cells_transportC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr?u8arr_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega:ZMicromega;ZArithProof04K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib7Mh_01117WdWkOut3fj0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj6C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indc59OSSVerify5KrLib7Mh_00708WdWkFmtN;nonfin_walkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib7Mh_01348WdWkFmtF4pfxbC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6ret_pcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame7outsideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6sub_fpC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame<munch_weakenC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec7evt_cutC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3stkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8ro_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3appC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem9upd_bytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5wmonoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr5u8arrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr6u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj7C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut3fj1C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib7Mh_00708WdWkFmtN5b_nanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00708WdWkFmtN5b_infC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic4True00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib7Mh_01117WdWkOut5fjunk00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut6zflagsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Theorem fmtfp_nonfin_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo p s h l fa B0 cap k lbf : Z) (G : word) (ibuf : list byte)
   (rpos rend wbase wfn bufp bsz mode lockv cookie : word) (J : fjunk),
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m -> (lo <= bv_unsigned sp - 4640)%Z -> (bv_unsigned sp < 2 ^ 63)%Z ->
  ro_cells rsegs m 0xc5ab8 [C8 (Z_to_bv 64 0xf8ac0)] -> ro_cells rsegs m 0xf8ac0 [C8 G] -> (0xf8ac8 <= lo)%Z ->
  (0 <= p < 2 ^ 31)%Z -> (0 <= s <= 1)%Z -> (0 <= h < 2 ^ 63)%Z -> (0 <= l < 2 ^ 64)%Z -> (h / 2 ^ 48 = 32767)%Z ->
  a0 = Z_to_bv 64 fa -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 (s * 9223372036854775808 + h) ->
  a3 = Z_to_bv 64 1 -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 0 -> a6 = Z_to_bv 64 103 -> a7 = Z_to_bv 64 0 ->
  fst_at m fa B0 cap k lbf ibuf rpos rend wbase wfn bufp bsz mode lockv cookie J -> fgeo (bv_unsigned sp) fa B0 cap -> (k + 4 <= cap)%Z ->
  evt rsegs (fun ms' => exists (sb : list byte) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' fc' m',
      (sb = b_inf \/ sb = b_nan) /\
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (s + 3)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (ret_pc ra) fc' None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (B0 + k, B0 + k + 4); (fa + 40, fa + 48)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ fst_at m' fa B0 cap (k + s + 3) lbf (upd_bytes ibuf (Z.to_nat k) (pfxb s ++ sb)) rpos rend wbase wfn bufp bsz mode lockv cookie J)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb0240) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdWkFmtNA ()) [] (Mh_0070_blobs1.kr_b_038 ())). Qed.

End WdWkFmtNA.
Module VdWkDg.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import VdMath.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VdWkDg () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbK47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions;bv_unsignedC79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C49OSSVerify5KrLib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC49OSSVerify5KrLib8PropExec9alu_sltiuC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C49OSSVerify5KrLib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorK4ELinuxProcessSemantics5Riscv5Instr5instr03C56Stdlib6ZArith6BinInt1Z4lxorC49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_xoriC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_lorC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;v_sltiu_b2zC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_subC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop05C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5instr0BC56Stdlib6ZArith6BinInt1Z3mulC49OSSVerify5KrLib8PropExec5v_mulC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5m_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divK4ELinuxProcessSemantics5Riscv5Instr5mulop01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC46Stdlib6ZArith4ZdivBZminus_mod_idemp_rK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:munch_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:wmono_reflC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_boundC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorI47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_NoneC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem2waC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr:u8arr_readC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr>u8arr_store_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3zxbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC79OSSVerify5KrLib2CJ3Lib7Mh_00393MemAzext_extract_byteC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_1'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses8or_morphC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6insideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkDg9fin1_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr3updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr:upd_lengthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib4Bool4Bool=negb_true_iffC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge8bv_ltu_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib6VdMath3VDM8land_W64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkDg<sub_mod_stepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr5u8arrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06K4ELinuxProcessSemantics5Riscv3Sem4core01C46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succI4ELinuxProcessSemantics5Riscv3Sem4core00C46Stdlib5Lists4List6nth_okK4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6shiftlK47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init5Logic4True01C46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkDg@ztb_unsigned_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC56Stdlib6ZArith6BinInt1Z3oppc59OSSVerify5KrLib7Mh_00706VdWkDg5tk_nzC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem4sx32C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells6cbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le4C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells7cell_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells5csizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_sllC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_sllC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem:length_le4C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_frameC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib7Mh_00597WdWkMem8sx32_ztbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkDgAztb_unsigned_add2C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c59OSSVerify5KrLib7Mh_00706VdWkDg8rw1_loopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame7outsideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6sub_fpC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib7SFModel<mod64_land63C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5aluop03c59OSSVerify5KrLib7Mh_00706VdWkDg9fin2_walkC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Ltac fix_sbw :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?c)) _) => change (Z_to_le_bytes 1 c) with [Z_to_bv 8 c]
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => change (le1 w) with [Z_to_bv 8 (bv_unsigned w)]
  end.
Ltac show_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => idtac "mem=" m end.
Ltac brs := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let B := fresh "B" in destruct c eqn:B end.

(* [comment removed for export] *)
Lemma fin1_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => exists (res : Z) a1' a2' a3' a4' a5',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0x3e290) fc None m (seg_rom rsegs) /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e210) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDg ()) [] (Mh_0070_blobs1.kr_b_039 ())). Qed.

Lemma fin2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => exists (res : Z) a1' a2' a3' a4' a5',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0x3e290) fc None m (seg_rom rsegs) /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e248) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDg ()) [] (Mh_0070_blobs1.kr_b_040 ())). Qed.

Open Scope Z_scope.
Lemma sub_mod_step D r tk : 0 <= D < 2 ^ 64 -> 0 <= r < 2 ^ 64 -> 1 <= tk <= (D - r) mod 2 ^ 64 ->
  (D - (r + tk) mod 2 ^ 64) mod 2 ^ 64 = (D - r) mod 2 ^ 64 - tk.
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDg ()) [] (Mh_0070_blobs1.kr_b_041 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma rw1_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) < 2 ^ 63)%Z ->
  ((bv_unsigned a0 - bv_unsigned t5) mod 2 ^ 64 <= Z.of_nat n)%Z ->
  (1 <= bv_unsigned a4 <= (bv_unsigned a0 - bv_unsigned t5) mod 2 ^ 64)%Z ->
  a6 = Z_to_bv 64 (buf + len) ->
  evt rsegs (fun ms' => exists (res : Z) t0' a1' a2' a3' a4' a5' a7' t5' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5' t6) F
               (Z_to_bv 64 0x3e290) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e0ec) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDg ()) [] (Mh_0070_blobs1.kr_b_042 ())). Qed.

Open Scope Z_scope.
Lemma tk_nz dv sh : dv = 100 \/ dv = 10 \/ dv = 1 -> 56 <= sh <= 59 -> 1 <= bv_unsigned (Z_to_bv 64 (Z.shiftl dv (Z.land sh 63))).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDg ()) [] (Mh_0070_blobs1.kr_b_043 ())). Qed.
Lemma ztb_unsigned_add k d : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 k) + d) = Z_to_bv 64 (k + d).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDg ()) [] (Mh_0070_blobs1.kr_b_044 ())). Qed.
Lemma ztb_unsigned_add2 k d e : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 k) + d + e) = Z_to_bv 64 (k + d + e).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDg ()) [] (Mh_0070_blobs1.kr_b_045 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma rw1_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 kap dv sh : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) < 2 ^ 63)%Z -> (Z.of_nat (length bs) < 2 ^ 31)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + Z.of_nat (length bs) <= kp)%Z -> (lenp + 4 <= buf \/ buf + Z.of_nat (length bs) <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (0 <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (0 <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z ->
  (bv_unsigned t5 < bv_unsigned a0)%Z -> (56 <= sh <= 59)%Z -> (dv = 100 \/ dv = 10 \/ dv = 1)%Z -> (1 <= kap <= 3)%Z -> (- 2 ^ 20 <= k0 <= 2 ^ 20)%Z ->
  t0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> t6 = Z_to_bv 64 dv -> a5 = Z_to_bv 64 sh -> t3 = Z_to_bv 64 kap ->
  evt rsegs (fun ms' => exists (res : Z) t0' t1' a1' a2' a3' a4' a5' a6' a7' t5' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5' t6) F
               (Z_to_bv 64 0x3e290) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs)); (kp, kp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + (kap - 1)))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)]
      /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e0bc) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDg ()) [] (Mh_0070_blobs1.kr_b_046 ())). Qed.

(* [comment removed for export] *)
Lemma rw2_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) < 2 ^ 63)%Z ->
  (bv_unsigned t4 < Z.of_nat n)%Z -> (1 <= bv_unsigned a1)%Z ->
  a6 = Z_to_bv 64 (buf + len) ->
  evt rsegs (fun ms' => exists (res : Z) t0' a1' a2' a3' a4' a5' a7' t3' t4' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6) F
               (Z_to_bv 64 0x3e290) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e1cc) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDg ()) [] (Mh_0070_blobs1.kr_b_047 ())). Qed.

(* [comment removed for export] *)
Lemma rw2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 kap : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) < 2 ^ 63)%Z -> (Z.of_nat (length bs) < 2 ^ 31)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + Z.of_nat (length bs) <= kp)%Z -> (lenp + 4 <= buf \/ buf + Z.of_nat (length bs) <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (0 <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (0 <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z ->
  (1 <= bv_unsigned a1)%Z -> (- 2 ^ 20 <= kap <= 2 ^ 20)%Z -> (- 2 ^ 20 <= k0 <= 2 ^ 20)%Z ->
  t0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> t4 = Z_to_bv 64 kap ->
  evt rsegs (fun ms' => exists (res : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6) F
               (Z_to_bv 64 0x3e290) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs)); (kp, kp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + kap))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)]
      /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e178) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_048 ())). Qed.

(* [comment removed for export] *)
Lemma loop2_walk : forall (k n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 sh Dl p2 : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (0 <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (0 <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (0 <= buf)%Z ->
  (n + k = 18)%nat -> (10 ^ Z.of_nat n <= Dl)%Z -> (Dl <= p2 < 2 ^ sh)%Z -> (56 <= sh <= 59)%Z -> (1 <= len <= 3 + Z.of_nat n)%Z -> (- 2 ^ 19 <= k0 <= 2 ^ 19)%Z ->
  t0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> t4 = Z_to_bv 64 (- Z.of_nat n) -> a5 = Z_to_bv 64 sh -> t5 = Z_to_bv 64 10 ->
  a0 = Z_to_bv 64 Dl -> a4 = Z_to_bv 64 p2 -> t2 = Z_to_bv 64 (2 ^ sh - 1) -> a1 = Z_to_bv 64 (2 ^ sh) ->
  evt rsegs (fun ms' => exists (res len' dk : Z) t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t6' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6') F
               (Z_to_bv 64 0x3e290) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + dk))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-18 <= dk <= 2)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e130) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_049 ())). Qed.


End VdWkDg.
Module VdWkDg2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VdWkDg2 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3eqbC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib7Mh_00597WdWkKit=swrap32_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_remuwC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Ltac no_vars c := match c with context [?x] => is_var x; fail 2 "open term" | _ => idtac end.
Ltac cbr := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  no_vars c; let v := eval vm_compute in c in change c with v; cbv iota end.

Open Scope Z_scope.
Definition dvk (j : nat) : Z := match j with 3%nat => 100 | 2%nat => 10 | _ => 1 end.
Lemma remuw_val (wx : word) (d : Z) : bv_unsigned wx < 2 ^ 31 -> 0 < d < 2 ^ 31 -> v_remuw wx (Z_to_bv 64 d) = Z_to_bv 64 (bv_unsigned wx mod d).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkDg2 ()) [] (Mh_0070_blobs1.kr_b_050 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma kloop_walk : forall (j : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 sh Dl p1 Wp1 : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (0 <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (0 <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (0 <= buf)%Z ->
  (1 <= j <= 3)%nat -> (56 <= sh <= 59)%Z -> (1 <= Dl <= Wp1)%Z -> (2 ^ sh <= Wp1 < 2 ^ 64)%Z -> (0 <= p1 < 10 * dvk j)%Z -> (0 <= len <= 3 - Z.of_nat j)%Z ->
  (len = 0 -> p1 = Wp1 / 2 ^ sh)%Z -> (- 2 ^ 19 <= k0 <= 2 ^ 19)%Z ->
  t0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> t4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 sh -> t5 = Z_to_bv 64 len ->
  a0 = Z_to_bv 64 Dl -> a4 = Z_to_bv 64 (Wp1 mod 2 ^ sh) -> t2 = Z_to_bv 64 (2 ^ sh - 1) -> a1 = Z_to_bv 64 (2 ^ sh) ->
  s0 = Z_to_bv 64 p1 -> t6 = Z_to_bv 64 (dvk j) -> t3 = Z_to_bv 64 (Z.of_nat j) -> s1 = Z_to_bv 64 0xcccccccd00000000 ->
  evt rsegs (fun ms' => exists (res len' dk : Z) t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (Z_to_bv 64 0x3e290) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + dk))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-18 <= dk <= 2)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3e06c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_051 ())). Qed.

End VdWkDg2.
Module VdWkDg3.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg2.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Ltac setreg_by n e t := let v := getreg n in replace v with e by t.

(* [comment removed for export] *)
Definition dg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo buf kp lenp k0 : Z) : machine_state -> Prop :=
  fun ms' => exists (res len' dk : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (bv_unsigned sp) [C8 (Z_to_bv 64 kp)] /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + dk))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-18 <= dk <= 2)%Z.

Lemma dg_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp k0 Wm W Wp E e1 e3 e5 : Z) (bs lb : list byte),
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 kp)] ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp + 8 <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp + 8 <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp + 8 <= buf)%Z ->
  (1 <= Wm <= Wp)%Z -> (W <= Wp)%Z -> (0 <= W)%Z -> (2 ^ 59 <= Wp <= 2 ^ 64 - 2)%Z -> (-59 <= E <= -56)%Z -> (- 2 ^ 19 <= k0 <= 2 ^ 19)%Z ->
  (0 <= e1 < 2 ^ 64)%Z -> (0 <= e3 < 2 ^ 64)%Z -> (0 <= e5 < 2 ^ 64)%Z -> bv_swrap 32 e1 = E -> bv_swrap 32 e3 = E -> bv_swrap 32 e5 = E ->
  a0 = Z_to_bv 64 Wm -> a1 = Z_to_bv 64 e1 -> a2 = Z_to_bv 64 W -> a3 = Z_to_bv 64 e3 -> a4 = Z_to_bv 64 Wp -> a5 = Z_to_bv 64 e5 ->
  a6 = Z_to_bv 64 buf -> a7 = Z_to_bv 64 lenp ->
  evt rsegs (dg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo buf kp lenp k0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3dfe0) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_052 ())). Qed.

End VdWkDg3.
Module VdWkG.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath VdTab. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdTab OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg3.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VdWkG () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC56Stdlib6ZArith6BinInt1Z4onesK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z9land_onesC59OSSVerify5KrLib6VdMath3VDM8land_W64C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Open Scope Z_scope.
Lemma land_W_M32 x : Z.land (Z.land x 18446744073709551615) 4294967295 = x mod 2 ^ 32.
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkG ()) [] (Mh_0070_blobs1.kr_b_053 ())). Qed.
Close Scope Z_scope.

Ltac setreg2 n e t := let v := getreg n in replace v with e by (symmetry; t).

(* [comment removed for export] *)
Definition g_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : word -> option byte)
    (lo buf kp lenp : Z) : machine_state -> Prop :=
  fun ms' => exists (res len' kz : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F'
               (ret_pc ra) fc' None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 kz)] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-343 <= kz <= 309)%Z /\ frm0 fc'.

(* [comment removed for export] *)
Lemma grisu_c2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (spz lo buf kp lenp mi mie pe P Wn sh : Z) (junk16 bs kb lb : list byte) (o_ra o_s0 o_s1 o_s2 o_s3 o_s4 o_s5 o_s6 : word),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo spz -> (lo + 48 <= spz)%Z -> (spz + 80 < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z -> (bv_unsigned o_ra mod 2 = 0)%Z ->
  rw_cells rsegs m spz [CB 16 junk16; C8 o_s6; C8 o_s5; C8 o_s4; C8 o_s3; C8 o_s2; C8 o_s1; C8 o_s0; C8 o_ra] ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (spz + 80 <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (spz + 80 <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (spz + 80 <= buf)%Z ->
  (1 <= mi)%Z -> (sh = mie - pe + 10)%Z -> (9 <= sh <= 62)%Z -> (mi * 2 ^ sh <= Wn * 2 ^ 11)%Z -> (Wn * 2 ^ 11 <= P * 2 ^ 10)%Z -> (2 ^ 63 <= P * 2 ^ 10 < 2 ^ 64)%Z ->
  (-1021 <= -50 - pe <= 1077)%Z -> (-2000 <= mie <= 2000)%Z -> (0 <= Wn)%Z -> (0 <= P)%Z ->
  a0 = Z_to_bv 64 (pe + 1) -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 kp -> a4 = Z_to_bv 64 mie -> a5 = Z_to_bv 64 pe -> a6 = Z_to_bv 64 Wn -> a7 = Z_to_bv 64 mi ->
  t1 = Z_to_bv 64 P -> t4 = Z_to_bv 64 18446744073709551615 -> s0 = Z_to_bv 64 buf -> s1 = Z_to_bv 64 lenp -> sp = Z_to_bv 64 spz ->
  evt rsegs (g_post o_ra (Z_to_bv 64 (spz + 80)) gp tp o_s0 o_s1 o_s2 o_s3 o_s4 o_s5 o_s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3daf4) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_054 ())). Qed.

End VdWkG.
Module VdWkGp.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath VdTab. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdTab OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkDg3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.VdWkG.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VdWkGp () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z:pow_succ_rK4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec7alu_andC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09I4ELinuxProcessSemantics5Riscv7Prelude4tree00C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC49OSSVerify5KrLib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr08K47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib6VdMath3VDM<land_pow2_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2ex01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01C59OSSVerify5KrLib6VdMath3VDM<land_pow2_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz01I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega6VarMap1t03C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge=bv_lts_zero_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtK4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C56Stdlib6ZArith6BinInt1Z9log2_specC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rK46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05C56Stdlib6ZArith4Znat5Z2Nat2idC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP4frm0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics5Riscv3Sem7reg_getC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr5u8arrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00705VdWkG6g_postC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc59OSSVerify5KrLib7Mh_00706VdWkGp<grisu_d_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00706VdWkGp<grisu_n_walkC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

(* [comment removed for export] *)
Lemma lpA_walk : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (X e : Z),
  (1 <= n)%nat -> (2 ^ 53 <= X * 2 ^ Z.of_nat n < 2 ^ 54)%Z -> (0 <= X)%Z ->
  a1 = Z_to_bv 64 4503599627370496 -> t1 = Z_to_bv 64 X -> a5 = Z_to_bv 64 e ->
  evt rsegs (fun ms' => exists a0',
      ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (X * 2 ^ Z.of_nat n)) t2 s0 s1 a0' a1 a2 a3 a4 (Z_to_bv 64 (e - Z.of_nat n)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0x3dab8) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3daa8) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkGp ()) [] (Mh_0070_blobs1.kr_b_055 ())). Qed.

(* [comment removed for export] *)
Lemma lpB_walk : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (Y e : Z),
  (1 <= n)%nat -> (2 ^ 52 <= Y * 2 ^ Z.of_nat n < 2 ^ 53)%Z -> (0 <= Y)%Z ->
  a6 = Z_to_bv 64 Y -> a0 = Z_to_bv 64 e ->
  evt rsegs (fun ms' => exists a1',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (e - Z.of_nat n)) a1' a2 a3 a4 a5 (Z_to_bv 64 (Y * 2 ^ Z.of_nat n)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0x3dacc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3dabc) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkGp ()) [] (Mh_0070_blobs1.kr_b_056 ())). Qed.


(* [comment removed for export] *)
Lemma grisu_n_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp u : Z) (bs kb lb : list byte),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo (bv_unsigned sp) -> (lo + 128 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (forall r, bv_unsigned r = 10%Z -> reg_get F r = Z_to_bv 64 u) -> (2 ^ 52 <= u < 2 ^ 63)%Z ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp <= buf)%Z ->
  a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 lenp -> a2 = Z_to_bv 64 kp ->
  evt rsegs (g_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3da20) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_057 ())). Qed.

Open Scope Z_scope.
Lemma dn_facts f : 1 <= f < 2 ^ 52 -> exists n : nat, (1 <= n <= 52)%nat /\ 2 ^ 52 <= f * 2 ^ Z.of_nat n < 2 ^ 53 /\ 2 ^ 53 <= (2 * f + 1) * 2 ^ Z.of_nat n < 2 ^ 54.
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkGp ()) [] (Mh_0070_blobs1.kr_b_058 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma grisu_d_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp u : Z) (bs kb lb : list byte),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo (bv_unsigned sp) -> (lo + 128 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (forall r, bv_unsigned r = 10%Z -> reg_get F r = Z_to_bv 64 u) -> (1 <= u < 2 ^ 52)%Z ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp <= buf)%Z ->
  a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 lenp -> a2 = Z_to_bv 64 kp ->
  evt rsegs (g_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3da20) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs1.kr_b_059 ())). Qed.

(* [comment removed for export] *)
Theorem grisu3_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp u : Z) (bs kb lb : list byte),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo (bv_unsigned sp) -> (lo + 128 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2 ^ 63)%Z -> (0xf8ac8 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (forall r, bv_unsigned r = 10%Z -> reg_get F r = Z_to_bv 64 u) -> (1 <= u < 2 ^ 63)%Z ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 < 2 ^ 63)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp <= kp)%Z -> (kp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp <= lenp)%Z -> (lenp + 4 < 2 ^ 63)%Z -> (bv_unsigned sp <= buf)%Z ->
  a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 lenp -> a2 = Z_to_bv 64 kp ->
  evt rsegs (g_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x3da20) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VdWkGp ()) [] (Mh_0070_blobs1.kr_b_060 ())). Qed.

End VdWkGp.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0047. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module WdStKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0047. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0047.FrmKeepNs0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0047.WdFrmAny.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdStKit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec6msteps00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP4frm0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec5mstepC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C69OSSVerify5KrLib7Mh_00478WdFrmAny4FRMA7step_fkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec:msteps_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0047:FrmKeepNs05FRMS05no_wxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0047:FrmKeepNs05FRMS0:fetch_safeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit;msteps_frm0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib5Lists4List2InC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_getK47Corelib4Init5Logic2eq01c59OSSVerify5KrLib7Mh_00707WdStKit3fsvC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib7Mh_00707WdStKit7fcs_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z4lxorK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z>lxor_nilpotentC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z7lxor_eqC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z;lxor_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula09C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7mod_modC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9rem_mul_rC56Stdlib6ZArith6BinInt1Z9land_onesI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00c59OSSVerify5KrLib7Mh_00707WdStKit3w32C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr3updC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init9Datatypes6lengthC56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesC47Corelib4Init5Peano2ltI47Corelib4Init5Peano2le00I47Corelib4Init5Logic2or00C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr<nth_error_ltC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr:upd_lengthC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic6eq_symC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List>nth_error_Nonec59OSSVerify5KrLib7Mh_00707WdStKit6nth_exC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions5bv_eqI47Corelib7Numbers7BinNums1N00C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z6shiftrC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC56Stdlib6ZArith6BinInt1Z7div_1_rC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismK47Corelib4Init5Logic2or02c59OSSVerify5KrLib7Mh_00707WdStKit=byte_of_mod32C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z=shiftr_shiftrC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00597WdWkKit>unsigned_neg64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit=swrap32_casesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem4sx32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit=unsigned_sx32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z:ones_equivC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z9mul_assocC56Stdlib6ZArith6BinInt1Z;pow_nonzeroC47Corelib4Init5Logic7and_indc59OSSVerify5KrLib7Mh_00707WdStKit7le4_anyC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z9log2_lxorC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

(* [comment removed for export] *)
Ltac setreg n e := let v := getreg n in replace v with e by (f_equal; lia).
Ltac no_vars c := match c with context [?x] => is_var x; fail 2 "open term" | _ => idtac end.
(* [comment removed for export] *)
Ltac cbr := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  no_vars c; let v := eval vm_compute in c in change c with v; cbv iota end.

(* [comment removed for export] *)
Lemma msteps_frm0 ms ms' : msteps rsegs ms ms' -> frm0 (ms_fcsr ms) -> frm0 (ms_fcsr ms').
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_061 ())). Qed.
Lemma evt_frm0 (Q : machine_state -> Prop) ms :
  evt rsegs Q ms -> frm0 (ms_fcsr ms) -> evt rsegs (fun ms' => Q ms' /\ frm0 (ms_fcsr ms')) ms.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_062 ())). Qed.

(* [comment removed for export] *)
Definition fcs_idx : list Z := [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%Z.
Definition fsv (F F' : bvmap 5 word) : Prop := forall r : bv 5, In (bv_unsigned r) fcs_idx -> bvmap_get r F' = bvmap_get r F.
Lemma fsv_refl F : fsv F F.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_063 ())). Qed.
Lemma fsv_trans F1 F2 F3 : fsv F1 F2 -> fsv F2 F3 -> fsv F1 F3.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_064 ())). Qed.

(* [comment removed for export] *)
Open Scope Z_scope.
Definition w32 (xs : list word) : Prop := forall i w, nth_error xs i = Some w -> 0 <= bv_unsigned w < 2 ^ 32.
Lemma xor_lt1 k a : 0 <= k -> 0 <= a -> (Z.lxor k a <? 1) = (k =? a).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_065 ())). Qed.
Lemma xor_gt0 k b : 0 <= k -> 0 <= b -> (0 <? Z.lxor k b) = negb (k =? b).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_066 ())). Qed.
Lemma land_W_2047 x : Z.land (Z.land x 18446744073709551615) 2047 = x mod 2048.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_067 ())). Qed.
Lemma land_2047 x : Z.land x 2047 = x mod 2048.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_068 ())). Qed.
Lemma w32_upd xs i v : w32 xs -> 0 <= v < 2 ^ 32 -> w32 (upd xs i (Z_to_bv 64 v)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_069 ())). Qed.
Lemma nth_ex {A} (xs : list A) i : (i < length xs)%nat -> exists w, nth_error xs i = Some w.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_070 ())). Qed.
Lemma land_pred_2047 k : 0 <= k < 2048 -> Z.land (bv_unsigned (Z_to_bv 64 (k - 1))) 2047 = (k - 1) mod 2048.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_071 ())). Qed.
Lemma mod_pred_step a k n : 0 <= a < 2048 -> 0 <= k < 2048 -> 0 <= n -> (k - a) mod 2048 = n + 1 -> ((k - 1) mod 2048 - a) mod 2048 = n.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_072 ())). Qed.
Lemma mod_diff0 a k : 0 <= a < 2048 -> 0 <= k < 2048 -> (k - a) mod 2048 = 0 -> k = a.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_073 ())). Qed.
Lemma byte_of_mod32 x d : (d = 1 \/ d = 256 \/ d = 65536 \/ d = 16777216) -> Z_to_bv 8 (x / d) = Z_to_bv 8 ((x mod 4294967296) / d).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_074 ())). Qed.
Lemma le4_any x : Z_to_le_bytes 4 x = le4 (Z_to_bv 64 (x mod 2 ^ 32)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_075 ())). Qed.
Lemma swrap32_cases s : 0 <= s < 2 ^ 32 -> bv_swrap 32 s = (if s <? 2 ^ 31 then s else s - 2 ^ 32).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_076 ())). Qed.
Lemma unsigned_sx32 (w : word) : bv_unsigned w < 2 ^ 32 ->
  bv_unsigned (sx32 w) = (if bv_unsigned w <? 2 ^ 31 then bv_unsigned w else bv_unsigned w + (2 ^ 64 - 2 ^ 32)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_077 ())). Qed.
Lemma wrap32_sx32 (w : word) : bv_unsigned w < 2 ^ 32 -> bv_wrap 32 (bv_unsigned (sx32 w)) = bv_unsigned w.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_078 ())). Qed.
Lemma land_sx32_mask (w : word) sh : bv_unsigned w < 2 ^ 32 -> 1 <= sh <= 31 ->
  Z.land (bv_unsigned (sx32 w)) (2 ^ sh - 1) = bv_unsigned w mod 2 ^ sh.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_079 ())). Qed.
Lemma landW_swrap32_zero s : 0 <= s < 2 ^ 32 -> (Z.land (bv_swrap 32 s) 18446744073709551615 = 0 <-> s = 0).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_080 ())). Qed.
Lemma le4_swrap32 s : 0 <= s < 2 ^ 32 -> le4 (Z_to_bv 64 (bv_swrap 32 s)) = le4 (Z_to_bv 64 s).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_081 ())). Qed.
Lemma lxor_lt_2048 k a : 0 <= k < 2048 -> 0 <= a < 2048 -> 0 <= Z.lxor k a < 2048.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit ()) [] (Mh_0070_blobs1.kr_b_082 ())). Qed.
Close Scope Z_scope.

End WdStKit.
Module WdStDag.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdVfSpec.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStKit.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

(* [comment removed for export] *)
Definition fkl (L : list Z) (F F' : bvmap 5 word) : Prop := forall r : bv 5, In (bv_unsigned r) L -> reg_get F' r = reg_get F r.
Lemma fkl_refl L F : fkl L F F. Proof. intros r _. reflexivity. Qed.
Lemma fkl_trans L F1 F2 F3 : fkl L F1 F2 -> fkl L F2 F3 -> fkl L F1 F3.
Proof. intros H1 H2 r Hr. rewrite (H2 r Hr). apply H1. exact Hr. Qed.
Lemma fkl_weaken L L' F F' : (forall x, In x L' -> In x L) -> fkl L F F' -> fkl L' F F'.
Proof. intros HS H r Hr. apply H. apply HS. exact Hr. Qed.
Lemma fkl_set L F F' (k : bv 5) v : ~ In (bv_unsigned k) L -> fkl L F F' -> fkl L F (bvmap_set k v F').
Proof.
  intros Hk H r Hr. rewrite reg_get_set_other; [apply H; exact Hr|]. intros E. apply Hk. rewrite E. exact Hr.
Qed.
(* [comment removed for export] *)
Definition fcs_no8 : list Z := [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%Z.
Lemma fkl_restore8 F0 F1 : fkl fcs_no8 F0 F1 -> fkl fcs_idx F0 (bvmap_set (Z_to_bv 5 8) (reg_get F0 (Z_to_bv 5 8)) F1).
Proof.
  intros H r Hr. destruct (Z.eq_dec (bv_unsigned r) 8) as [E|N].
  - replace r with (Z_to_bv 5 8) by (apply bv_eq; rewrite E; reflexivity). apply reg_get_set_same.
  - rewrite reg_get_set_other; [|intros E; apply N; rewrite <- E; reflexivity]. apply H.
    unfold fcs_idx in Hr. unfold fcs_no8. cbn [In] in *. destruct Hr as [Hr|Hr]; [exfalso; apply N; symmetry; exact Hr | exact Hr].
Qed.
Ltac fk_solve :=
  repeat (apply fkl_set; [ let H := fresh in intros H; cbn [In] in H; repeat (destruct H as [H|H]; [discriminate H|]); exact H | ]);
  first [ eassumption | apply fkl_refl | (eapply fkl_weaken; [|eassumption]; let H := fresh in intros ? H; cbn [In fcs_idx fcs_no8] in *; tauto) ].

(* [comment removed for export] *)
Definition vff_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (lo fr : Z) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - fr, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ fkl fcs_idx F F'.

Definition vff_spec (pc fr : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc m lo,
    stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m -> (lo <= bv_unsigned sp - fr)%Z -> (0 <= fr)%Z -> frm0 fc -> (bv_unsigned ra mod 2 = 0)%Z ->
    evt rsegs (vff_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo fr m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Ltac vbr := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c; cbv iota end.
Ltac dag_go tbl := repeat (first
  [ lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => is_Zlit pc; tbl pc end
  | lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => fix_store_lit end
  | vbr ]).
Ltac fix_ret := try (lazymatch goal with
             | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
                 replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
             end).
(* [comment removed for export] *)
Ltac vcall SPEC :=
  lazymatch goal with
  | FZ : frm0 ?fc |- evt ?segs _ (MS _ _ _ ?fc _ ?m _) =>
      eapply evt_cut;
      [ eapply evt_frm0; [ eapply SPEC | exact FZ ]; rewrite ?unsigned_small64 by lia; try eassumption; try lia
      | cbv beta; let ms' := fresh "ms'" in let PO := fresh "PO" in let FZ' := fresh "FZn" in
        intros ms' [PO FZ']; unfold vf_post in PO; rewrite ?unsigned_small64 in PO by lia; revert FZ'; revert ms' PO;
        post_call segs m; clear FZ; intros FZ; cbn [ms_fcsr] in FZ; fix_ret ]
  end.
(* [comment removed for export] *)
Ltac vcallf SPEC :=
  lazymatch goal with
  | FZ : frm0 ?fc |- evt ?segs _ (MS _ ?Fc _ ?fc _ ?m _) =>
      eapply evt_cut;
      [ eapply evt_frm0; [ eapply SPEC | exact FZ ]; rewrite ?unsigned_small64 by lia; try eassumption; try lia; try reflexivity
      | cbv beta; let ms' := fresh "ms'" in let PO := fresh "PO" in let FZ' := fresh "FZn" in
        intros ms' [PO FZ']; unfold vff_post in PO; rewrite ?unsigned_small64 in PO by lia; revert FZ'; revert ms' PO;
        post_call segs m; clear FZ; intros FZ; cbn [ms_fcsr] in FZ; fix_ret;
        lazymatch goal with
        | FKc : fkl fcs_idx Fc ?Fn, FK : fkl ?L ?F0 ?Fb |- _ =>
            let FK' := fresh "FK" in
            assert (FK' : fkl L F0 Fn) by (apply (fkl_trans L F0 Fc Fn); [ solve [fk_solve] | eapply fkl_weaken; [ | exact FKc ]; let H := fresh in intros ? H; cbn [In fcs_idx fcs_no8] in *; tauto ]);
            clear FKc FK; rename FK' into FK
        | _ => idtac
        end ]
  end.
Ltac dag_go2 tbl fin := repeat (first
  [ lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => is_Zlit pc; tbl pc end
  | lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => fix_store_lit end
  | vbr | fin ]).

End WdStDag.
Module WdStKit2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdStKit2 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00707WdStKit6nth_exC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List6nth_okC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions8bv_swrapI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z8le_transK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_00597WdWkKit=swrap32_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem4sx32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit;wrap32_sx32C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_divuwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z7mod_addc59OSSVerify5KrLib7Mh_00707WdStKit=unsigned_sx32C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03c59OSSVerify5KrLib7Mh_00708WdStKit24zchkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib7Mh_00708WdStKit25rem9wC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3remC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith4Znat5Z2Nat2idc59OSSVerify5KrLib7Mh_00708WdStKit27zchk_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqc59OSSVerify5KrLib7Mh_00708WdStKit29rem9w_tabC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00708WdStKit25rpm9wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00708WdStKit24rpm9C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic7and_indC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Program6Basics4implc59OSSVerify5KrLib7Mh_00708WdStKit29rpm9w_tabC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_Reflexive".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma divuw_sx32 (w : word) (i : Z) : bv_unsigned w < 2 ^ 32 -> 2 <= i < 2 ^ 31 ->
  v_divuw (sx32 w) (Z_to_bv 64 i) = Z_to_bv 64 (bv_unsigned w / i).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit2 ()) [] (Mh_0070_blobs1.kr_b_083 ())). Qed.
(* [comment removed for export] *)
Lemma subw_rem_sx32 (w : word) (i : Z) : bv_unsigned w < 2 ^ 32 -> 2 <= i < 2 ^ 31 ->
  bv_swrap 32 (bv_unsigned (sx32 w) - bv_unsigned w / i * i) = bv_unsigned w mod i.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit2 ()) [] (Mh_0070_blobs1.kr_b_084 ())). Qed.

(* [comment removed for export] *)
Definition q9w (rp : Z) : Z :=
  Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.land rp 18446744073709551615 * 954437177))) 33
          + Z.shiftr (Z.land (Z.land rp 18446744073709551615 * 954437177) 18446744073709551615) 63) 18446744073709551615.
Definition rem9w (rp : Z) : Z :=
  bv_swrap 32 (Z.land (bv_swrap 32 (Z.land rp 18446744073709551615 - q9w rp)) 18446744073709551615 - Z.land (Z.shiftl (q9w rp) 3) 18446744073709551615).
Definition rpm9 (rp : Z) : Z := if rp <? 0 then Z.rem rp 9 + 9 else Z.rem rp 9.
Definition rpm9w (rp : Z) : Z :=
  bv_swrap 32 (Z.land (Z.rem rp 9) 18446744073709551615 + Z.land (Z.land (Z.shiftr (bv_signed (Z_to_bv 64 rp)) 63) 18446744073709551615) 9).
Fixpoint zchk (P : Z -> bool) (n : nat) (z : Z) : bool := match n with O => true | S n' => andb (P z) (zchk P n' (z + 1)) end.
Lemma zchk_ok : forall P n z rp, zchk P n z = true -> z <= rp < z + Z.of_nat n -> P rp = true.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit2 ()) [] (Mh_0070_blobs1.kr_b_085 ())). Qed.
Lemma rem9w_tab : zchk (fun rp => rem9w rp =? Z.rem rp 9) (Z.to_nat 6144) (-4096) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit2 ()) [] (Mh_0070_blobs1.kr_b_086 ())). Qed.
Lemma rem9w_ok rp : -4096 <= rp < 2048 -> rem9w rp = Z.rem rp 9.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit2 ()) [] (Mh_0070_blobs1.kr_b_087 ())). Qed.
Lemma rpm9w_tab : zchk (fun rp => orb (Z.rem rp 9 =? 0) (andb (andb (rpm9w rp =? rpm9 rp) (andb (1 <=? rpm9 rp) (rpm9 rp <=? 8))) ((rp - rpm9 rp + 9) mod 9 =? 0)))
                         (Z.to_nat 6144) (-4096) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit2 ()) [] (Mh_0070_blobs1.kr_b_088 ())). Qed.
Lemma rpm9w_ok rp : -4096 <= rp < 2048 -> Z.rem rp 9 <> 0 -> rpm9w rp = rpm9 rp /\ 1 <= rpm9 rp <= 8 /\ (rp - rpm9 rp + 9) mod 9 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStKit2 ()) [] (Mh_0070_blobs1.kr_b_089 ())). Qed.

End WdStKit2.
Module WdStExp.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkFmtB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStKit2.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdStExp () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00707WdStKit6nth_exC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List9nth_errorC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02c59OSSVerify5KrLib7Mh_00707WdStExp7digs_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedc59OSSVerify5KrLib7Mh_00707WdStExp4isdgC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib5Arith8PeanoNat3Nat7add_0_rC46Stdlib5Lists4List6nth_okI47Corelib4Init5Peano2le00C56Stdlib6ZArith4Znat5Nat2Z6inj_lec59OSSVerify5KrLib7Mh_00707WdStExp5isdgbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4bool02K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic5False00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula0:C56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00597WdWkKit>unsigned_neg64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC59OSSVerify5KrLib7Mh_00597WdWkKit=swrap32_smallC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto4kind02I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z4landC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivBZminus_mod_idemp_rC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

(* [comment removed for export] *)
Definition isdg (c : Z) : Prop := (48 <= c <= 57)%Z.
Definition digs_at (bz : list byte) (i : Z) (n : nat) : Prop :=
  forall t : nat, (t < n)%nat -> exists b, nth_error bz (Z.to_nat i + t)%nat = Some b /\ isdg (bv_unsigned b).
Lemma digs_at_S bz i n : (0 <= i)%Z -> digs_at bz i (S n) -> digs_at bz (i + 1) n.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStExp ()) [] (Mh_0070_blobs1.kr_b_090 ())). Qed.
Lemma digs_at_0 bz i n : digs_at bz i (S n) -> exists b, nth_error bz (Z.to_nat i) = Some b /\ isdg (bv_unsigned b).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStExp ()) [] (Mh_0070_blobs1.kr_b_091 ())). Qed.
Lemma digs_at_le bz i n n' : (n' <= n)%nat -> digs_at bz i n -> digs_at bz i n'.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStExp ()) [] (Mh_0070_blobs1.kr_b_092 ())). Qed.

Definition isdgb (c : Z) : bool := (48 <=? c)%Z && (c <=? 57)%Z.
Lemma isdgb_true c : isdg c -> isdgb c = true.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStExp ()) [] (Mh_0070_blobs1.kr_b_093 ())). Qed.
Lemma isdgb_false c : ~ isdg c -> isdgb c = false.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStExp ()) [] (Mh_0070_blobs1.kr_b_094 ())). Qed.
Lemma isdgb_spec c : if isdgb c then isdg c else ~ isdg c.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStExp ()) [] (Mh_0070_blobs1.kr_b_095 ())). Qed.
Lemma dlt10 c : (0 <= c < 256)%Z -> bv_ltu (Z_to_bv 64 (bv_swrap 32 (c + -48))) (Z_to_bv 64 10) = isdgb c.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStExp ()) [] (Mh_0070_blobs1.kr_b_096 ())). Qed.
Lemma dgt9 c : (0 <= c < 256)%Z -> bv_ltu (Z_to_bv 64 9) (Z_to_bv 64 (bv_swrap 32 (c + -48))) = negb (isdgb c).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStExp ()) [] (Mh_0070_blobs1.kr_b_097 ())). Qed.

(* [comment removed for export] *)
Ltac eqb_false_tac :=
  apply bv_eqb_neq; let EQ := fresh "EQ" in intros EQ;
  first [ apply (f_equal bv_unsigned) in EQ; rewrite !unsigned_small64 in EQ by lia; lia
        | apply (f_equal bv_signed) in EQ; rewrite !Z_to_bv_signed, !bv_swrap_small in EQ by (unfold bv_half_modulus, bv_modulus; cbn -[Z.pow Z.rem Z.mul Z.add Z.sub Z.opp]; lia); lia ].
Ltac br_neq := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  lazymatch c with
  | negb (bv_eqb ?a ?b) => let H := fresh "BR" in assert (H : bv_eqb a b = false) by eqb_false_tac; rewrite H; cbn [negb]; cbv iota; clear H
  | bv_eqb ?a ?b => let H := fresh "BR" in assert (H : bv_eqb a b = false) by eqb_false_tac; rewrite H; cbv iota; clear H
  end end.
Ltac br_eq := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  lazymatch c with
  | context [bv_eqb ?a ?b] => let H := fresh "BR" in assert (H : bv_eqb a b = true) by (replace b with a by (f_equal; lia); apply bv_eqb_refl); rewrite H; cbn [negb]; cbv iota; clear H
  end end.

(* [comment removed for export] *)
Ltac rwc_irr := match goal with H : rw_cells _ ?m ?a ?cs |- rw_cells _ ?m' ?a' ?cs' =>
  first [ constr_eq cs cs'; replace a' with a by lia; exact H
        | lazymatch cs with [C8 (Z_to_bv 64 ?v)] => lazymatch cs' with [C8 (Z_to_bv 64 ?v')] =>
            replace a' with a by lia; replace v' with v by lia; exact H end end ] end.
Ltac cell8_irr := rwc_irr.
(* [comment removed for export] *)
Ltac txrd i Hb :=
  lazymatch goal with TXT : u8ro _ ?m ?s ?bz |- _ =>
    pose proof (u8ro_read rsegs m s bz i _ (wa (s + i)) TXT Hb ltac:(lia) eq_refl) as RD end.

Lemma digs_at_shift bz0 i n i' : digs_at bz0 i n -> (0 <= i <= i')%Z -> (i' <= i + Z.of_nat n)%Z -> digs_at bz0 i' (Z.to_nat (i + Z.of_nat n - i')).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStExp ()) [] (Mh_0070_blobs1.kr_b_098 ())). Qed.
Lemma sgn_ltu_a d : isdg d -> bv_ltu (Z_to_bv 64 (-11)) (Z_to_bv 64 (bv_swrap 32 (d + -58))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStExp ()) [] (Mh_0070_blobs1.kr_b_099 ())). Qed.
Lemma sgn_ltu_b d : isdg d -> bv_ltu (Z_to_bv 64 (bv_swrap 32 (d + -58))) (Z_to_bv 64 (-10)) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_WdStExp ()) [] (Mh_0070_blobs1.kr_b_100 ())). Qed.

Lemma neg_landW (y : Z) : Z_to_bv 64 (0 - Z.land y 18446744073709551615) = Z_to_bv 64 (- y).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStExp ()) [] (Mh_0070_blobs1.kr_b_101 ())). Qed.

Section Se.
Variables (fa s : Z) (bz : list byte).
Hypothesis Hfa : (0 <= fa /\ fa + 208 < 2 ^ 63)%Z.
Hypothesis Hs : (fa + 272 <= s /\ s + Z.of_nat (length bz) < 2 ^ 63)%Z.   (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma se_lz : forall (n : nat) (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (i : Z) (b0 : byte),
  mem_inv rsegs m -> u8ro rsegs m s bz ->
  rw_cells rsegs m (fa + 8) [C8 (Z_to_bv 64 (s + i))] -> rw_cells rsegs m (fa + 184) [C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 0)] ->
  (0 <= i)%Z -> digs_at bz i n -> nth_error bz (Z.to_nat i + n)%nat = Some b0 -> ~ isdg (bv_unsigned b0) ->
  evt rsegs (fun ms' => exists a0' a1' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) s1 a0' a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 10) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0xb6880) fc None m' (seg_rom rsegs)
      /\ munch [(fa + 8, fa + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' (fa + 8) [C8 (Z_to_bv 64 (s + i + Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 10) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xb6860) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Se"] (Mh_0070_blobs1.kr_b_102 ())). Qed.

(* [comment removed for export] *)
Lemma se_ly : forall (n : nat) (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (i y c : Z) (b0 : byte),
  mem_inv rsegs m -> u8ro rsegs m s bz ->
  rw_cells rsegs m (fa + 8) [C8 (Z_to_bv 64 (s + i))] -> rw_cells rsegs m (fa + 184) [C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 0)] ->
  (0 <= i)%Z -> digs_at bz i n -> nth_error bz (Z.to_nat i + n)%nat = Some b0 -> ~ isdg (bv_unsigned b0) ->
  (0 <= y < 92233720368547758)%Z -> isdg c ->
  evt rsegs (fun ms' => exists (i' y' c1 : Z) (s3' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) (Z_to_bv 64 y') (Z_to_bv 64 c1) (Z_to_bv 64 (bv_swrap 32 (c1 + -48))) a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 9) s3' s4 (Z_to_bv 64 92233720368547758) (Z_to_bv 64 10) s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0xb6840) fc None m' (seg_rom rsegs)
      /\ munch [(fa + 8, fa + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' (fa + 8) [C8 (Z_to_bv 64 (s + i'))]
      /\ (i + 1 <= i' <= i + Z.of_nat n + 1)%Z /\ (exists b1, nth_error bz (Z.to_nat (i' - 1)) = Some b1 /\ bv_unsigned b1 = c1)
      /\ (isdg c1 -> i' <= i + Z.of_nat n)%Z /\ (~ isdg c1 -> i' = i + Z.of_nat n + 1)%Z /\ (0 <= y' < 2 ^ 60)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) (Z_to_bv 64 y) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 9) (Z_to_bv 64 c) s4 (Z_to_bv 64 92233720368547758) (Z_to_bv 64 10) s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xb67ec) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Se"] (Mh_0070_blobs1.kr_b_103 ())). Qed.

(* [comment removed for export] *)
Lemma se_lx : forall (n : nat) (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (i x c : Z) (b0 : byte),
  mem_inv rsegs m -> u8ro rsegs m s bz ->
  rw_cells rsegs m (fa + 8) [C8 (Z_to_bv 64 (s + i))] -> rw_cells rsegs m (fa + 184) [C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 0)] ->
  (0 <= i)%Z -> digs_at bz i n -> nth_error bz (Z.to_nat i + n)%nat = Some b0 -> ~ isdg (bv_unsigned b0) ->
  (0 <= x < 214748364)%Z -> isdg c ->
  evt rsegs (fun ms' => exists (i' x' c1 : Z) (a1' s2' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) (Z_to_bv 64 x') (Z_to_bv 64 (bv_swrap 32 (c1 + -48))) a1' a2 a3 a4 a5 a6 a7
                    s2' (Z_to_bv 64 c1) s4 (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 214748364) s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0xb67d8) fc None m' (seg_rom rsegs)
      /\ munch [(fa + 8, fa + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' (fa + 8) [C8 (Z_to_bv 64 (s + i'))]
      /\ (i + 1 <= i' <= i + Z.of_nat n + 1)%Z /\ (exists b1, nth_error bz (Z.to_nat (i' - 1)) = Some b1 /\ bv_unsigned b1 = c1)
      /\ (isdg c1 -> i' <= i + Z.of_nat n)%Z /\ (~ isdg c1 -> i' = i + Z.of_nat n + 1)%Z /\ (0 <= x' < 2 ^ 31)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) (Z_to_bv 64 x) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 c) s3 s4 (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 214748364) s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xb6780) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Se"] (Mh_0070_blobs1.kr_b_104 ())). Qed.

(* [comment removed for export] *)
Lemma scanexp_walk : forall (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (spw lo i : Z) (ne : nat) (bsg b0 : byte),
  mem_inv rsegs m -> u8ro rsegs m s bz ->
  rw_cells rsegs m (fa + 8) [C8 (Z_to_bv 64 (s + i))] -> rw_cells rsegs m (fa + 184) [C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 0)] ->
  stk rsegs m lo spw -> (lo + 80 <= spw)%Z -> (spw <= fa)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (0 <= i)%Z -> nth_error bz (Z.to_nat i) = Some bsg -> (bv_unsigned bsg = 43 \/ bv_unsigned bsg = 45)%Z ->
  (1 <= ne)%nat -> digs_at bz (i + 1) ne -> nth_error bz (Z.to_nat (i + 1) + ne)%nat = Some b0 -> ~ isdg (bv_unsigned b0) ->
  evt rsegs (fun ms' => exists (e10 : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR ra (Z_to_bv 64 spw) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 e10) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(spw - 80, spw); (fa + 8, fa + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo spw
      /\ rw_cells rsegs m' (fa + 8) [C8 (Z_to_bv 64 (s + i + 1 + Z.of_nat ne))] /\ (- 2 ^ 60 < e10 < 2 ^ 60)%Z)
    (MS (mkR ra (Z_to_bv 64 spw) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fa) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xb665c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Se"] (Mh_0070_blobs2.kr_b_105 ())). Qed.

End Se.

End WdStExp.
Module WdStFrame.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0111.WdWkOut OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdVfSpec.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStDag.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdStFrame () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00707WdStKit6nth_exC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List6nth_okC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr6u32arrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;stk_releaseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib7Mh_00597WdWkMem=stk_of_u32arrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic3and00C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame9stk_mergeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3stkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr4u32sC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8bytes_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u32s_lengthC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr8u32s_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMem9wr_at_appC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib5Lists4List:length_appC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K46Stdlib9micromega:ZMicromega;ZArithProof01K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le8C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells;cells_bytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem:length_le8C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01117WdWkOut=cells_reshapeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMemBu32arr_of_rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMem>words_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMemEwords_of_bytes_lengthC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic9False_indc59OSSVerify5KrLib7Mh_00709WdStFrame:u32arr_appC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic4True01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Lemma fs_release m (lo spz : Z) cs ys ct :
  stk rsegs m lo spz -> rw_cells rsegs m spz cs -> cells_size cs = 96%nat ->
  u32arr rsegs m (spz + 96) ys -> length ys = 2050%nat ->
  rw_cells rsegs m (spz + 8296) ct -> cells_size ct = 120%nat -> (lo <= spz)%Z ->
  stk rsegs m lo (spz + 8416).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStFrame ()) [] (Mh_0070_blobs2.kr_b_106 ())). Qed.

Ltac ynorm := rewrite ?land_W_2047, ?land_2047; rewrite ?(Z.shiftl_mul_pow2 _ 2) by lia; change (2 ^ 2)%Z with 4%Z.
(* [comment removed for export] *)
Ltac yabs :=
  lazymatch goal with
  | H : u32arr _ _ _ (upd ?ys0 ?k ?v), LY : length ?ys0 = ?n |- _ =>
      let ys' := fresh "ys" in let LY' := fresh "LY" in
      assert (LY' : length (upd ys0 k v) = n) by (rewrite upd_length; exact LY);
      set (ys' := upd ys0 k v) in *; clearbody ys'; clear LY; try clear ys0
  end.
(* [comment removed for export] *)
Ltac yst r :=
  ynorm;
  let v := getreg r in
  lazymatch v with
  | Z_to_bv 64 ?E =>
    lazymatch E with
    | context [(?i * 4)%Z] =>
      let R := fresh "Ridx" in assert (R : (0 <= i < 2048)%Z) by (first [lia | (apply Z.mod_pos_bound; lia)]);
      lazymatch goal with
      | YS : u32arr _ ?m ?B ?ys, LY : length ?ys = _ |- _ =>
        let RBy := fresh "RBy" in let SOK := fresh "SOK" in
        pose proof (u32arr_bound rsegs m B ys YS) as RBy;
        pose proof (u32arr_store_ok rsegs m B ys (i + 1) (wa (B + 4 * (i + 1))) YS ltac:(lia) eq_refl) as SOK;
        zstep;
        let YS' := fresh "YS" in
        pose proof (u32arr_write rsegs m B ys (i + 1) (Z_to_bv 64 0) YS ltac:(lia)) as YS'; clear YS; store_done; yabs; clear RBy
      end
    end
  end.
(* [comment removed for export] *)
Ltac yld r :=
  ynorm;
  let v := getreg r in
  lazymatch v with
  | Z_to_bv 64 ?E =>
    lazymatch E with
    | context [(?i * 4)%Z] =>
      let R := fresh "Ridx" in assert (R : (0 <= i < 2048)%Z) by (first [lia | (apply Z.mod_pos_bound; lia)]);
      lazymatch goal with
      | YS : u32arr _ ?m ?B ?ys, LY : length ?ys = _ |- _ =>
        let w := fresh "w" in let Hw := fresh "Hw" in let RBy := fresh "RBy" in let RD := fresh "RD" in
        destruct (nth_ex ys (Z.to_nat (i + 2)) ltac:(lia)) as (w & Hw);
        pose proof (u32arr_bound rsegs m B ys YS) as RBy;
        pose proof (u32arr_read rsegs m B ys (i + 2) w (wa (B + 4 * (i + 2))) YS Hw ltac:(lia) eq_refl) as RD;
        setreg r (Z_to_bv 64 (B + 4 * (i + 2)));
        zstep; clear RD RBy Hw
      end
    end
  end.

(* [comment removed for export] *)
Lemma u32arr_app m (A : Z) (xs ys : list word) :
  u32arr rsegs m A xs -> u32arr rsegs m (A + 4 * Z.of_nat (length xs)) ys -> u32arr rsegs m A (xs ++ ys).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStFrame ()) [] (Mh_0070_blobs2.kr_b_107 ())). Qed.
Lemma view_join m (B : Z) (v : word) (xs : list word) :
  rw_cells rsegs m B [C8 v] -> u32arr rsegs m (B + 8) xs -> exists w1 w2, u32arr rsegs m B (w1 :: w2 :: xs).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStFrame ()) [] (Mh_0070_blobs2.kr_b_108 ())). Qed.

(* [comment removed for export] *)
Ltac setreg1 n e :=
  lazymatch goal with
  | |- evt ?s ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
      let R' := eval cbv beta iota delta [tset mkR] in (tset p e R) in
      let v := getreg n in
      replace (MS R F pc fc rv m ro) with (MS R' F pc fc rv m ro)
        by (let Ev := fresh "Ev" in assert (Ev : e = v) by (f_equal; lia); rewrite Ev; reflexivity)
  end.

End WdStFrame.
Module WdStAl.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkFmtB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStDag OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStFrame.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdStAl () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00707WdStKit6nth_exC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List6nth_okC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K4ELinuxProcessSemantics5Riscv5Instr5instr0;K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions8bv_swrapC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu32C49OSSVerify5KrLib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BI4ELinuxProcessSemantics5Riscv7Prelude4tree00C49OSSVerify5KrLib8PropExec5v_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC49OSSVerify5KrLib8PropExec5m_mulC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK4ELinuxProcessSemantics5Riscv5Instr5instr05C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib7Mh_00597WdWkKit>unsigned_neg64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge8bv_eqb_ZC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith6BinInt1Z9mul_assocC79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMemAswrap32_landW_addC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz07C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Section Al.
Variables (ra gp tp s0 s1 s4 s5 s6 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variable X : Z.      (* [comment removed for export] *)
Hypothesis HX : (104 < X)%Z /\ (X + 8192 < 2 ^ 63)%Z.
Notation sp := (Z_to_bv 64 (X - 104)) (only parsing).

(* [comment removed for export] *)
Lemma al_step : forall (t1 t2 t3 t4 t5 t6 a0 a1 a2 s2 s7 : word) m (z k c p10 q : Z) (xs : list word) (w : word),
  mem_inv rsegs m -> u32arr rsegs m X xs -> length xs = 2048%nat -> w32 xs ->
  (0 <= k < z)%Z -> (z <= 8)%Z -> (0 <= c < 1000000000)%Z -> (10 <= p10 <= 100000000)%Z -> (p10 * q = 1000000000)%Z ->
  nth_error xs (Z.to_nat k) = Some w -> (k = 0 -> c = 0 /\ p10 <= bv_unsigned w)%Z ->
  evt rsegs (fun ms' => exists (v c' : Z) t1' t2' t3' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (X + 4 * (k + 1))) t1' t2' s0 s1 a0 a1 a2 (Z_to_bv 64 (k + 1)) (Z_to_bv 64 c') (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 q)
                    s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6) F
               (Z_to_bv 64 (if (k + 1 =? z)%Z then 0xb55a4 else 0xb557c)) fc None m' (seg_rom rsegs)
      /\ munch [(X, X + 8192)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ u32arr rsegs m' X (upd xs (Z.to_nat k) (Z_to_bv 64 v)) /\ (0 <= v < 2 ^ 32)%Z /\ (0 <= c' < 1000000000)%Z /\ (k = 0 -> 1 <= v)%Z)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (X + 4 * k)) t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 k) (Z_to_bv 64 c) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 q)
             s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb557c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Al"] (Mh_0070_blobs2.kr_b_109 ())). Qed.

Definition al_post (a0 a1 a2 s2 s7 : word) (t4 t5 t6 : word) (m : word -> option byte) (z p10 q : Z) : machine_state -> Prop :=
  fun ms' => exists (c' : Z) (xs' : list word) (w0' : word) t1' t2' t3' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (X + 4 * z)) t1' t2' s0 s1 a0 a1 a2 (Z_to_bv 64 z) (Z_to_bv 64 c') (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 q)
                    s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6) F
               (Z_to_bv 64 0xb55a4) fc None m' (seg_rom rsegs)
      /\ munch [(X, X + 8192)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ u32arr rsegs m' X xs' /\ length xs' = 2048%nat /\ w32 xs' /\ (0 <= c' < 1000000000)%Z
      /\ nth_error xs' 0 = Some w0' /\ (1 <= bv_unsigned w0')%Z.

Lemma al_loop : forall (n : nat) (t1 t2 t3 t4 t5 t6 a0 a1 a2 s2 s7 : word) m (z k c p10 q : Z) (xs : list word) (w0 : word),
  mem_inv rsegs m -> u32arr rsegs m X xs -> length xs = 2048%nat -> w32 xs ->
  (0 <= k < z)%Z -> (z <= 8)%Z -> (0 <= c < 1000000000)%Z -> (10 <= p10 <= 100000000)%Z -> (p10 * q = 1000000000)%Z ->
  (z - k = Z.of_nat (S n))%Z ->
  nth_error xs 0 = Some w0 -> (k = 0 -> c = 0 /\ p10 <= bv_unsigned w0)%Z -> (1 <= k -> 1 <= bv_unsigned w0)%Z ->
  evt rsegs (al_post a0 a1 a2 s2 s7 t4 t5 t6 m z p10 q)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (X + 4 * k)) t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 k) (Z_to_bv 64 c) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 q)
             s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb557c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Al"] (Mh_0070_blobs2.kr_b_110 ())). Qed.

Ltac ms_eq := cbv [mkR]; repeat (first [ reflexivity | lia | (progress f_equal) ]).

(* [comment removed for export] *)
Lemma dz_loop : forall (n : nat) (t0 t1 t2 t3 t4 t5 t6 a5 a6 a7 s2 s3 s7 : word) m (i K : Z) (xs : list word) (w0 : word),
  mem_inv rsegs m -> u32arr rsegs m X xs -> length xs = 2048%nat -> w32 xs ->
  (0 <= i <= 8)%Z -> (i = Z.of_nat n)%Z -> (i <= K <= 8)%Z -> nth_error xs 0 = Some w0 -> (1 <= bv_unsigned w0)%Z ->
  evt rsegs (fun ms' => exists (zf : Z) (wz : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zf * 4294967296)) (Z_to_bv 64 (K + 1 - zf + 1)) (Z_to_bv 64 (X + 4 * (zf - 2))) (Z_to_bv 64 zf) (Z_to_bv 64 (-4294967296)) (sx32 wz) a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb54cc) fc None m (seg_rom rsegs)
      /\ (1 <= zf <= i + 1)%Z /\ nth_error xs (Z.to_nat (zf - 1)) = Some wz /\ (1 <= bv_unsigned wz)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ((i + 2) * 4294967296)) (Z_to_bv 64 (K - i)) (Z_to_bv 64 (X + 4 * i)) (Z_to_bv 64 (i + 2)) (Z_to_bv 64 (-4294967296)) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb54b4) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Al"] (Mh_0070_blobs2.kr_b_111 ())). Qed.

(* [comment removed for export] *)
Lemma fd_loop : forall (n : nat) (t0 t1 t2 t3 t4 t5 t6 a0 a3 a4 a5 a6 a7 s2 s3 s7 : word) m (v : Z),
  (0 <= v)%Z -> (v * 10 ^ Z.of_nat (S n) < 2 ^ 63)%Z -> (n <= 8)%nat ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (v * 10 ^ Z.of_nat (S n))) (Z_to_bv 64 10) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 0) s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb526c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 v) (Z_to_bv 64 10) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (- Z.of_nat (S n))) s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb5260) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdStAl ()) ["Al"] (Mh_0070_blobs2.kr_b_112 ())). Qed.

End Al.

End WdStAl.
Module WdVfFmodl.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdVfSpec.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdVfDivtf3. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfLeaf OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfLetf2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfMultf3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfAddtf3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdVfDivtf3.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStDag.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfFloatsitf OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfFpclassifyl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfExtendsftf2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdVfFmodl () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00707WdStKit6nth_exC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List6nth_okC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3divK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC59OSSVerify5KrLib7Mh_00597WdWkKit<land_W_rangeC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusI47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag3fklC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP4frm0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5wmonoC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells6cbytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6ret_pcC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;stk_releaseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revI47Corelib4Init5Logic2ex00c59OSSVerify5KrLib7Mh_00709WdVfFmodl9body_postC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3stkC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics5Riscv3Sem4core01C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le8C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8load_u64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells7cell_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells5csizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem2waC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib7Mh_00707WdStKit7fcs_idxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w1_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib7Mh_00658WdVfSpec7vf_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0066=WdVfFloatsitf<floatsitf_vfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit8evt_frm0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame7outsideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6sub_fpC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame<munch_weakenC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0066:WdVfMultf39multf3_vfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl9blk_b6a90C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec7evt_cutC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula07C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C47Corelib4Init5Logic9False_indK4ELinuxProcessSemantics5Riscv5Instr5instr09C49OSSVerify5KrLib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC49OSSVerify5KrLib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C56Stdlib6ZArith6BinInt1Z3lorC49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6alu_orC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C49OSSVerify5KrLib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C49OSSVerify5KrLib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z?mul_mod_distr_lC56Stdlib6ZArith6BinInt1Z8mul_commK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqK46Stdlib9micromega=RingMicromega5Psatz01C47Corelib4Init5Logic5proj2C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge8bv_eqb_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith6BinInt1Z:pow_succ_rI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03C56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09K46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1Z7eqb_neqc59OSSVerify5KrLib7Mh_00709WdVfFmodl9blk_b6c74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00258WdSfBase=lor_shift_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_commC59OSSVerify5KrLib7Mh_00597WdWkKit<land_W_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge9zr_shiftrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC45stdpp9bitvector;definitions8bv_swrapC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09I47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I46Stdlib;setoid_ring<Ring_polynom3Mon00K46Stdlib9micromega=RingMicromega3Op204C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C47Corelib4Init5Logic3iffK46Stdlib;setoid_ring<Ring_polynom5PExpr06C56Stdlib6ZArith6BinInt1Z6eq_decK4ELinuxProcessSemantics5Riscv5Instr5instr01C49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC49OSSVerify5KrLib8PropExec5b_luiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=div_small_iffC56Stdlib6ZArith6BinInt1Z9div_smallC47Corelib4Init9Datatypes4negbc59OSSVerify5KrLib7Mh_00709WdVfFmodl8fm_loop2C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega7EnvRing5PExpr06C69OSSVerify5KrLib2CJ3Lib7SFModel;signed_of_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_addC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP=Z_lor_lt_pow2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z<lor_eq_0_iffc59OSSVerify5KrLib7Mh_00709WdVfFmodl9blk_b6c30C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z9add_opp_rC59OSSVerify5KrLib7Mh_00597WdWkMem=ztb_landW_addC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula09K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_andC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specc59OSSVerify5KrLib7Mh_00709WdVfFmodl8fm_loop1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl8fm_post1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkKit?land_mask48_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK4ELinuxProcessSemantics5Riscv5Instr5aluop0:C49OSSVerify5KrLib:WdVfDivtf39divtf3_vfC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0RC4ELinuxProcessSemantics5Riscv3Sem7nan_boxC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP9bv_lit_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0066?WdVfExtendsftf2>extendsftf2_vfC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2Inc59OSSVerify5KrLib7Mh_00707WdStDag7fkl_setC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl<unsigned_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl7shr_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00709WdVfFmodl7fm_headC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr6fmvdir02K4ELinuxProcessSemantics5Riscv5Instr4ffmt01I47Corelib7Numbers7BinNums8positive00".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Section Body.
Variables (sp gp tp s9 s10 s11 : word) (rao s0o s1o s2o s3o s4o s5o s6o s7o s8o : word) (F0 : bvmap 5 word) (m0 : word -> option byte) (lo : Z).
Hypothesis LO : (0 <= lo /\ lo + 192 <= bv_unsigned sp)%Z.
Hypothesis Hra : (bv_unsigned rao mod 2 = 0)%Z.
Definition body_post : machine_state -> Prop := fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' (fc' : bv 32) m',
  ms' = MS (mkR rao sp gp tp t0' t1' t2' s0o s1o a0' a1' a2' a3' a4' a5' a6' a7' s2o s3o s4o s5o s6o s7o s8o s9 s10 s11 t3' t4' t5' t6') F' (ret_pc rao) fc' None m' (seg_rom rsegs)
  /\ munch [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
  /\ fkl fcs_idx F0 F' /\ frm0 fc'.
Ltac fr_fin := idtac; lazymatch goal with |- evt _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
  lazymatch goal with FRx : rw_cells _ _ (bv_unsigned sp + -80)%Z _, STx : stk _ _ _ _ |- _ => release_frame FRx STx (bv_unsigned sp) end;
  apply evt_done; unfold body_post; do 18 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [solve [fk_solve] | eassumption] end.
Ltac fr_intro := pose proof (bv_unsigned_in_range _ sp) as RSP; change (bv_modulus 64) with (2 ^ 64)%Z in RSP.
Lemma shr_rng (x k : Z) : (0 <= x < 2 ^ 64)%Z -> (33 <= k <= 63)%Z -> (0 <= Z.shiftr x k < 2 ^ 31)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfFmodl ()) ["Body"] (Mh_0070_blobs2.kr_b_113 ())). Qed.
Lemma land15_rng (x : Z) : (0 <= Z.land x 32767 < 2 ^ 31)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfFmodl ()) ["Body"] (Mh_0070_blobs2.kr_b_114 ())). Qed.
Lemma landW_rng (x : Z) : (0 <= Z.land x 18446744073709551615 < 2 ^ 64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfFmodl ()) ["Body"] (Mh_0070_blobs2.kr_b_115 ())). Qed.
Lemma unsigned_rng (w : word) : (0 <= bv_unsigned w < 2 ^ 64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfFmodl ()) ["Body"] (Mh_0070_blobs2.kr_b_116 ())). Qed.
Ltac fm_rng := repeat match goal with
  | |- context [Z.shiftr ?x ?k] => lazymatch goal with H : (0 <= Z.shiftr x k < 2 ^ 31)%Z |- _ => fail | _ =>
       let R := fresh "Rs" in assert (R : (0 <= Z.shiftr x k < 2 ^ 31)%Z) by (apply shr_rng; [first [apply landW_rng | apply unsigned_rng | lia] | lia]) end
  | |- context [Z.land ?x 32767] => lazymatch goal with H : (0 <= Z.land x 32767 < 2 ^ 31)%Z |- _ => fail | _ =>
       let R := fresh "Rs" in pose proof (land15_rng x) as R end
  end.

Lemma blk_b6a90 : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) ,
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6acc) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfFmodl ()) ["Body"] (Mh_0070_blobs2.kr_b_117 ())). Qed.

Lemma blk_b6c30 : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) ,
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6c6c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfFmodl ()) ["Body"] (Mh_0070_blobs2.kr_b_118 ())). Qed.

Lemma blk_b6c74 : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) ,
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6cb0) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Body"] (Mh_0070_blobs2.kr_b_119 ())). Qed.

Lemma fm_loop2 : forall (n : nat) (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (xhi xlo : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  (0 <= xhi < 2 ^ 48)%Z ->
  (0 <= xlo < 2 ^ 64)%Z ->
  (2 ^ 112 <= (xhi * 2 ^ 64 + xlo) * 2 ^ Z.of_nat n)%Z ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 xhi) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 xlo) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6c94) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfFmodl ()) ["Body"] (Mh_0070_blobs2.kr_b_120 ())). Qed.
Lemma fm_post1 : forall (ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (xhi xlo yhi ylo : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  (0 <= xhi < 2 ^ 63)%Z ->
  (0 <= xlo < 2 ^ 64)%Z ->
  (2 ^ 48 <= yhi < 2 ^ 49)%Z ->
  (0 <= ylo < 2 ^ 64)%Z ->
  (0 < xhi * 2 ^ 64 + xlo < 2 * (yhi * 2 ^ 64 + ylo))%Z ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 yhi) (Z_to_bv 64 xhi) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ylo) (Z_to_bv 64 xlo) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6c50) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfFmodl ()) ["Body"] (Mh_0070_blobs2.kr_b_121 ())). Qed.
Lemma fm_loop1 : forall (n : nat) (ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (xhi xlo yhi ylo ex ey : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  (0 <= xhi < 2 ^ 63)%Z ->
  (0 <= xlo < 2 ^ 64)%Z ->
  (2 ^ 48 <= yhi < 2 ^ 49)%Z ->
  (0 <= ylo < 2 ^ 64)%Z ->
  (0 < xhi * 2 ^ 64 + xlo < 2 * (yhi * 2 ^ 64 + ylo))%Z ->
  (- 2 ^ 31 <= ey < ex)%Z ->
  (ex < 2 ^ 31)%Z ->
  (ex - ey <= Z.of_nat n)%Z ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 yhi) (Z_to_bv 64 xhi) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ylo) (Z_to_bv 64 xlo) s4 s5 s6 (Z_to_bv 64 ex) (Z_to_bv 64 ey) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6be8) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Body"] (Mh_0070_blobs2.kr_b_122 ())). Qed.
Lemma fm_head : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ex ey : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  (- 2 ^ 31 <= ey < 2 ^ 31)%Z ->
  (- 2 ^ 31 <= ex < 2 ^ 31)%Z ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ex) (Z_to_bv 64 ey) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6bac) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfFmodl ()) ["Body"] (Mh_0070_blobs2.kr_b_123 ())). Qed.

Ltac fm_to_loop := eapply fm_head; try eassumption; try solve [fk_solve]; try (fm_rng; lia).

Lemma blk_b6a70 : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) ,
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6aac) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfFmodl ()) ["Body"] (Mh_0070_blobs2.kr_b_124 ())). Qed.

Lemma blk_b6b40 : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ex : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  (- 2 ^ 31 <= ex < 2 ^ 31)%Z ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ex) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6b7c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfFmodl ()) ["Body"] (Mh_0070_blobs2.kr_b_125 ())). Qed.

Lemma blk_b6a40 : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) ,
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6a7c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Body"] (Mh_0070_blobs2.kr_b_126 ())). Qed.

End Body.

Theorem fmodl_vff : vff_spec 0xb6a50 192.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) [] (Mh_0070_blobs2.kr_b_127 ())). Qed.

End WdVfFmodl.
Module WdVfScalbn.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdVfSpec.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStDag.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdVfScalbn () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00707WdStKit6nth_exC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List6nth_okC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib7Mh_00707WdStDag3fklC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP4frm0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions;bv_unsignedC49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics5Riscv7Prelude4tree02C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08I4ELinuxProcessSemantics5Riscv7Prelude4tree00C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr0:C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0RK4ELinuxProcessSemantics5Riscv5Instr5instr0LC4ELinuxProcessSemantics5Riscv3Sem7reg_getK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4fgetC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP6fari_dC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem7with_pcC4ELinuxProcessSemantics5Riscv3Sem6accrueC4ELinuxProcessSemantics5Riscv3Sem4fsetK4ELinuxProcessSemantics5Riscv3Sem3eff01C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;interp_eff0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lift_resultC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4execC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP9rmode_dynC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP;exec_fari_dC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP;frm0_accrueC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Fpu;fflags_bitsK4ELinuxProcessSemantics5Riscv5Instr5instr04C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6ret_pcC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7add_0_rC49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes4list01C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notc59OSSVerify5KrLib7Mh_00707WdStDag7fkl_setC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib7Mh_0070:WdVfScalbn9body_postC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP=freg_get_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP>freg_get_otherC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP6fmul_dC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP7fari_flC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv3Fpu5rmode01K4ELinuxProcessSemantics5Riscv5Instr6fariop03C4ELinuxProcessSemantics5Riscv3Fpu:fmt_doubleK47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib7Mh_00707WdStKit7fcs_idxC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr6fmvdir02K4ELinuxProcessSemantics5Riscv5Instr4ffmt02I4ELinuxProcessSemantics5Riscv3Sem3eff00C4ELinuxProcessSemantics5Riscv3Sem2w1C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w1_litC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums8positive00I47Corelib4Init5Logic4True00K47Corelib7Numbers7BinNums1Z03K4ELinuxProcessSemantics5Riscv5Instr5instr03c59OSSVerify5KrLib7Mh_0070:WdVfScalbn9blk_ad288C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr02C49OSSVerify5KrLib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC49OSSVerify5KrLib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0II47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C79OSSVerify5KrLib2CJ3Lib7Mh_00395Image:ro_bytes_bC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses;rew_iff_revC79OSSVerify5KrLib2CJ3Lib7Mh_00395Image>ro_cells_imageC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8ro_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells6cbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP9bv_lit_eqC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells7cell_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells5csizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem2waC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@ro_cells_read_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr01C49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C49OSSVerify5KrLib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C49OSSVerify5KrLib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070:WdVfScalbn9blk_ad270C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070:WdVfScalbn9blk_ad238C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelI4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1N01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes:comparison00I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloc59OSSVerify5KrLib7Mh_00707WdStDag8vff_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag8fkl_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070:WdVfScalbn9blk_ad20cC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:munch_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:wmono_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag8vff_specC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5wmonoC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Section Body.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F0 : bvmap 5 word) (m : word -> option byte).
Hypothesis MI : mem_inv rsegs m.
Definition body_post : machine_state -> Prop := fun ms' => exists a0' a1' F' (fc' : bv 32),
  ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m (seg_rom rsegs)
  /\ fkl fcs_idx F0 F' /\ frm0 fc'.
Ltac sb_fin := idtac; lazymatch goal with |- evt _ _ (MS _ _ (ret_pc _) _ _ _ _) => apply evt_done; unfold body_post; do 4 eexists; split; [reflexivity|]; split; [solve [fk_solve] | eassumption] end.

Lemma blk_ad288 : forall (a0 a1 : word) (F : bvmap 5 word) (fc : bv 32),
  fkl fcs_idx F0 F ->
  frm0 fc ->
  evt rsegs body_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xad2c4) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfScalbn ()) ["Body"] (Mh_0070_blobs2.kr_b_128 ())). Qed.

Lemma blk_ad238 : forall (a0 a1 : word) (F : bvmap 5 word) (fc : bv 32),
  fkl fcs_idx F0 F ->
  frm0 fc ->
  evt rsegs body_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xad274) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfScalbn ()) ["Body"] (Mh_0070_blobs2.kr_b_129 ())). Qed.

Lemma blk_ad270 : forall (a0 a1 : word) (F : bvmap 5 word) (fc : bv 32),
  fkl fcs_idx F0 F ->
  frm0 fc ->
  evt rsegs body_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xad2ac) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfScalbn ()) ["Body"] (Mh_0070_blobs2.kr_b_130 ())). Qed.

Lemma blk_ad20c : forall (a0 a1 : word) (F : bvmap 5 word) (fc : bv 32),
  fkl fcs_idx F0 F ->
  frm0 fc ->
  evt rsegs body_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xad248) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfScalbn ()) ["Body"] (Mh_0070_blobs2.kr_b_131 ())). Qed.

End Body.

Theorem scalbn_vff : vff_spec 0xad248 0.
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfScalbn ()) [] (Mh_0070_blobs2.kr_b_132 ())). Qed.

End WdVfScalbn.
Module WdVfScalbnl.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdVfSpec.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdVfDivtf3. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfLeaf OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfLetf2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfMultf3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfAddtf3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdVfDivtf3.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStDag.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0066.WdVfExtenddftf2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdVfScalbnl () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00707WdStKit6nth_exC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List6nth_okC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3stkC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag3fklC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP4frm0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5wmonoC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070;WdVfScalbnl9blk_b6dfcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStKit7fcs_idxC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib7Mh_0070;WdVfScalbnl9body_postC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5instr01C45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z6shiftlC49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08I4ELinuxProcessSemantics5Riscv7Prelude4tree00C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070;WdVfScalbnl9blk_b6df8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3powC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3mrdC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:munch_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:wmono_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame9stk_carveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag8vff_postC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells;cb_split_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cb_splitC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells5csizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells6cbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem:length_le8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphI47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses;rew_iff_revC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6insideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame9stk_writeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag8fkl_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070;WdVfScalbnl9blk_b6d10C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6ret_pcC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag8vff_specC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib5Lists7ListDef5skipnC79OSSVerify5KrLib2CJ3Lib7Mh_00394StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells7cell_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic2ex01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K4ELinuxProcessSemantics5Riscv5Instr5msize04K46Stdlib9micromega=RingMicromega3Op205".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Section Body.
Variables (sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (rao s0o s1o s2o : word) (F0 : bvmap 5 word) (m0 : word -> option byte) (lo : Z).
Hypothesis LO : (0 <= lo /\ lo + 112 <= bv_unsigned sp)%Z.
Hypothesis Hra : (bv_unsigned rao mod 2 = 0)%Z.
Definition body_post : machine_state -> Prop := fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' (fc' : bv 32) m',
  ms' = MS (mkR rao sp gp tp t0' t1' t2' s0o s1o a0' a1' a2' a3' a4' a5' a6' a7' s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc rao) fc' None m' (seg_rom rsegs)
  /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
  /\ fkl fcs_idx F0 F' /\ frm0 fc'.
Ltac fr_fin := idtac; lazymatch goal with |- evt _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
  lazymatch goal with FRx : rw_cells _ _ (bv_unsigned sp + -32)%Z _, STx : stk _ _ _ _ |- _ => release_frame FRx STx (bv_unsigned sp) end;
  apply evt_done; unfold body_post; do 18 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [solve [fk_solve] | eassumption] end.
Ltac fr_intro := pose proof (bv_unsigned_in_range _ sp) as RSP; change (bv_modulus 64) with (2 ^ 64)%Z in RSP.

Lemma blk_b6dfc : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -32) ->
  rw_cells rsegs m (bv_unsigned sp + -32) [C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6e38) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Body"] (Mh_0070_blobs2.kr_b_133 ())). Qed.

Lemma blk_b6df8 : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -32) ->
  rw_cells rsegs m (bv_unsigned sp + -32) [C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6e34) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfScalbnl ()) ["Body"] (Mh_0070_blobs2.kr_b_134 ())). Qed.

Lemma blk_b6d60 : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -32) ->
  rw_cells rsegs m (bv_unsigned sp + -32) [C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6d9c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfScalbnl ()) ["Body"] (Mh_0070_blobs2.kr_b_135 ())). Qed.

Lemma blk_b6dbc : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -32) ->
  rw_cells rsegs m (bv_unsigned sp + -32) [C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6df8) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfScalbnl ()) ["Body"] (Mh_0070_blobs2.kr_b_136 ())). Qed.

Lemma blk_b6d10 : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -32) ->
  rw_cells rsegs m (bv_unsigned sp + -32) [C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  fkl fcs_idx F0 F ->
  frm0 fc ->
  munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m0 m ->
  wmono rsegs m0 m ->
  evt rsegs body_post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6d4c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Body"] (Mh_0070_blobs2.kr_b_137 ())). Qed.

End Body.

Theorem scalbnl_vff : vff_spec 0xb6d38 112.
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfScalbnl ()) [] (Mh_0070_blobs2.kr_b_138 ())). Qed.

End WdVfScalbnl.
Module WdStUp.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdWkFmtB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStKit.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Section Up.
Variables (ra sp gp tp s0 s1 s4 s6 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variable X : Z.      (* [comment removed for export] *)
Hypothesis HX : (0 < X)%Z /\ (X + 8192 < 2 ^ 63)%Z.

Lemma up_step : forall (t0 t1 t2 t3 t4 t5 t6 a7 s5 s7 : word) m (a z k c : Z) (xs : list word) (w : word),
  mem_inv rsegs m -> u32arr rsegs m X xs -> length xs = 2048%nat -> w32 xs ->
  (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> (0 <= k < 2048)%Z -> (0 <= c < 2 ^ 32)%Z ->
  Z.land (bv_unsigned t4) 2047 = k -> nth_error xs (Z.to_nat k) = Some w ->
  evt rsegs (fun ms' => exists (v c' z' : Z) t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 z) (Z_to_bv 64 k) s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 19342813113834067)
                    (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) (Z_to_bv 64 c') a7 (Z_to_bv 64 z') (Z_to_bv 64 a) s4 s5 s6 s7 s8 s9 s10 s11
                    (Z_to_bv 64 ((z + -1) mod 2048)) (Z_to_bv 64 (k - 1)) t5' t6') F
               (Z_to_bv 64 (if (k =? a)%Z then 0xb5610 else 0xb5640)) fc None m' (seg_rom rsegs)
      /\ munch [(X, X + 8192)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ u32arr rsegs m' X (upd xs (Z.to_nat k) (Z_to_bv 64 v))
      /\ (0 <= v < 2 ^ 32)%Z /\ (0 <= c' < 2 ^ 32)%Z /\ (0 <= z' < 2048)%Z
      /\ (z' = z \/ (z' = k /\ k <> a))
      /\ (k = a -> z' = z)
      /\ (c' = 0 -> v = bv_unsigned w * 2 ^ 29 + c)%Z
      /\ (2 <= bv_unsigned w -> 1 <= c')%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 19342813113834067)
             (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) (Z_to_bv 64 c) a7 (Z_to_bv 64 z) (Z_to_bv 64 a) s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0xb5640) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Up"] (Mh_0070_blobs2.kr_b_139 ())). Qed.

Definition up_pass_post (t0 a7 s5 s7 : word) (m : word -> option byte) (a : Z) (wa0 : word) : machine_state -> Prop :=
  fun ms' => exists (c' z' : Z) (xs' : list word) t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 z') (Z_to_bv 64 a) s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 19342813113834067)
                    (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) (Z_to_bv 64 c') a7 (Z_to_bv 64 z') (Z_to_bv 64 a) s4 s5 s6 s7 s8 s9 s10 s11
                    (Z_to_bv 64 ((z' + -1) mod 2048)) (Z_to_bv 64 (a - 1)) t5' t6') F
               (Z_to_bv 64 0xb5610) fc None m' (seg_rom rsegs)
      /\ munch [(X, X + 8192)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ u32arr rsegs m' X xs' /\ length xs' = 2048%nat /\ w32 xs'
      /\ (0 <= c' < 2 ^ 32)%Z /\ (0 <= z' < 2048)%Z /\ z' <> a
      /\ (c' = 0 -> exists va, nth_error xs' (Z.to_nat a) = Some va /\ bv_unsigned wa0 * 2 ^ 29 <= bv_unsigned va)%Z
      /\ (2 <= bv_unsigned wa0 -> 1 <= c')%Z.

Lemma up_pass : forall (d : nat) (t0 t1 t2 t3 t4 t5 t6 a7 s5 s7 : word) m (a z k c : Z) (xs : list word) (wa0 : word),
  mem_inv rsegs m -> u32arr rsegs m X xs -> length xs = 2048%nat -> w32 xs ->
  (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> (0 <= k < 2048)%Z -> (0 <= c < 2 ^ 32)%Z ->
  Z.land (bv_unsigned t4) 2047 = k -> ((k - a) mod 2048 = Z.of_nat d)%Z -> z <> a ->
  nth_error xs (Z.to_nat a) = Some wa0 ->
  evt rsegs (up_pass_post t0 a7 s5 s7 m a wa0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 19342813113834067)
             (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) (Z_to_bv 64 c) a7 (Z_to_bv 64 z) (Z_to_bv 64 a) s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0xb5640) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Up"] (Mh_0070_blobs2.kr_b_140 ())). Qed.

Definition up_inv_post (m : word -> option byte) (rp : Z) (wa0 : word) : machine_state -> Prop :=
  fun ms' => exists (a' z' rp' : Z) (xs' : list word) (wa' : word) t1' t2' t3' t4' t5' t6' a6' s5' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 rp') t1' t2' s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 19342813113834067)
                    (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) a6' (Z_to_bv 64 (X + 4 * a')) (Z_to_bv 64 z') (Z_to_bv 64 a') s4 s5' s6 (Z_to_bv 64 rp') s8 s9 s10 s11
                    t3' t4' t5' t6') F
               (Z_to_bv 64 0xb561c) fc None m' (seg_rom rsegs)
      /\ munch [(X, X + 8192)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ u32arr rsegs m' X xs' /\ length xs' = 2048%nat /\ w32 xs'
      /\ (0 <= a' < 2048)%Z /\ (0 <= z' < 2048)%Z /\ z' <> a'
      /\ nth_error xs' (Z.to_nat a') = Some wa' /\ (1 <= bv_unsigned wa')%Z
      /\ (rp' = rp + 9 \/ (rp' = rp /\ bv_unsigned wa0 < 2 /\ 2 <= bv_unsigned wa'))%Z.

Lemma up_round : forall (t1 t2 t3 t4 t5 t6 a6 s5 : word) m (a z rp : Z) (xs : list word) (wa0 : word),
  mem_inv rsegs m -> u32arr rsegs m X xs -> length xs = 2048%nat -> w32 xs ->
  (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> z <> a -> (-4000 <= rp <= 36)%Z ->
  nth_error xs (Z.to_nat a) = Some wa0 -> (1 <= bv_unsigned wa0)%Z ->
  evt rsegs (up_inv_post m rp wa0)
    (MS (mkR ra sp gp tp (Z_to_bv 64 rp) t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 19342813113834067)
             (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) a6 (Z_to_bv 64 (X + 4 * a)) (Z_to_bv 64 z) (Z_to_bv 64 a) s4 s5 s6 (Z_to_bv 64 rp) s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0xb562c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Up"] (Mh_0070_blobs2.kr_b_141 ())). Qed.

Definition up_exit_post (m : word -> option byte) (rp : Z) : machine_state -> Prop :=
  fun ms' => exists (a' z' rp' : Z) (xs' : list word) (wa' : word) t0' t1' t2' t3' t4' t5' t6' a6' a7' s5' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 19342813113834067)
                    (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) a6' a7' (Z_to_bv 64 z') (Z_to_bv 64 a') s4 s5' s6 (Z_to_bv 64 rp') s8 s9 s10 s11
                    t3' t4' t5' t6') F
               (Z_to_bv 64 0xb572c) fc None m' (seg_rom rsegs)
      /\ munch [(X, X + 8192)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ u32arr rsegs m' X xs' /\ length xs' = 2048%nat /\ w32 xs'
      /\ (0 <= a' < 2048)%Z /\ (0 <= z' < 2048)%Z /\ z' <> a'
      /\ nth_error xs' (Z.to_nat a') = Some wa' /\ (1 <= bv_unsigned wa')%Z
      /\ (36 <= rp')%Z /\ (rp' <= Z.max rp 45)%Z /\ ((rp' - rp) mod 9 = 0)%Z.

Lemma up_loop : forall (n : nat) (t1 t2 t3 t4 t5 t6 a6 s5 : word) m (a z rp : Z) (xs : list word) (wa0 : word),
  mem_inv rsegs m -> u32arr rsegs m X xs -> length xs = 2048%nat -> w32 xs ->
  (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> z <> a -> (-4000 <= rp <= 4000)%Z ->
  nth_error xs (Z.to_nat a) = Some wa0 -> (1 <= bv_unsigned wa0)%Z ->
  (2 * (45 - rp) + (if (2 <=? bv_unsigned wa0)%Z then 0 else 1) <= Z.of_nat n)%Z ->
  evt rsegs (up_exit_post m rp)
    (MS (mkR ra sp gp tp (Z_to_bv 64 rp) t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 19342813113834067)
             (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) a6 (Z_to_bv 64 (X + 4 * a)) (Z_to_bv 64 z) (Z_to_bv 64 a) s4 s5 s6 (Z_to_bv 64 rp) s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0xb561c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Up"] (Mh_0070_blobs2.kr_b_142 ())). Qed.

End Up.

End WdStUp.
Module WdVfTrunctfdf2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0065.WdVfSpec.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0070.WdStDag.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdVfTrunctfdf2 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00707WdStKit6nth_exC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List6nth_okC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib7Mh_00707WdStDag3fklC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP4frm0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6shiftrK4ELinuxProcessSemantics5Riscv7Prelude4tree02C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z3addC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlI4ELinuxProcessSemantics5Riscv7Prelude4tree00C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C56Stdlib6ZArith6BinInt1Z3lorC49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK4ELinuxProcessSemantics5Riscv5Instr5instr0RK4ELinuxProcessSemantics5Riscv5Instr5instr04C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6ret_pcC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes4list01C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notc59OSSVerify5KrLib7Mh_00707WdStDag7fkl_setC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib7Mh_0070>WdVfTrunctfdf29body_postC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_lorC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge7zr_wordC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge9zr_shiftrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C59OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_reprogSrc_jsoncons_fuzz_msgpack_encoder_repro_loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib7Mh_00707WdStKit7fcs_idxC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr6fmvdir02K4ELinuxProcessSemantics5Riscv5Instr4ffmt02K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv3Sem2w1C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w1_litC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums8positive00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool01C49OSSVerify5KrLib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z4lxorC49OSSVerify5KrLib8PropExec5v_xorC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_xorC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070>WdVfTrunctfdf29blk_b7114C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop06C56Stdlib6ZArith6BinInt1Z6moduloC49OSSVerify5KrLib8PropExec5v_srlC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_srlC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_sraiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_sraiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_andC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbc59OSSVerify5KrLib7Mh_0070>WdVfTrunctfdf29blk_b722cC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC49OSSVerify5KrLib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge9zr_land_lC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge?zb_shl_shr_landC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib7SFModel<mod64_land63C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib7Numbers7BinNums1Z03C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_sllC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_sllC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070>WdVfTrunctfdf29blk_b71e4C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge7zr_lxorC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5instr01C49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC49OSSVerify5KrLib8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C49OSSVerify5KrLib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C49OSSVerify5KrLib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070>WdVfTrunctfdf29blk_b70e0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocc59OSSVerify5KrLib7Mh_0070>WdVfTrunctfdf29blk_b7104C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag8vff_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag8fkl_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0070>WdVfTrunctfdf29blk_b7058C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:munch_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:wmono_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00707WdStDag8vff_specC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3stkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5wmonoC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Plain_loaded_segments (only parsing).

Section Body.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F0 : bvmap 5 word) (m : word -> option byte).
Hypothesis MI : mem_inv rsegs m.
Definition body_post : machine_state -> Prop := fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' (fc' : bv 32),
  ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m (seg_rom rsegs)
  /\ fkl fcs_idx F0 F' /\ frm0 fc'.
Ltac lf_fin := idtac; lazymatch goal with |- evt _ _ (MS _ _ (ret_pc _) _ _ _ _) => apply evt_done; unfold body_post; do 17 eexists; split; [reflexivity|]; split; [solve [fk_solve] | eassumption] end.

Lemma blk_b7114 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  fkl fcs_idx F0 F ->
  frm0 fc ->
  evt rsegs body_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7150) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfTrunctfdf2 ()) ["Body"] (Mh_0070_blobs2.kr_b_143 ())). Qed.

Lemma blk_b722c : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  fkl fcs_idx F0 F ->
  frm0 fc ->
  evt rsegs body_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7268) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfTrunctfdf2 ()) ["Body"] (Mh_0070_blobs2.kr_b_144 ())). Qed.

Lemma blk_b71e4 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  fkl fcs_idx F0 F ->
  frm0 fc ->
  evt rsegs body_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7220) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfTrunctfdf2 ()) ["Body"] (Mh_0070_blobs2.kr_b_145 ())). Qed.

Lemma blk_b71ac : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  fkl fcs_idx F0 F ->
  frm0 fc ->
  evt rsegs body_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb71e8) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfTrunctfdf2 ()) ["Body"] (Mh_0070_blobs2.kr_b_146 ())). Qed.

Lemma blk_b70e0 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  fkl fcs_idx F0 F ->
  frm0 fc ->
  evt rsegs body_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb711c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0070 ()) ["Body"] (Mh_0070_blobs2.kr_b_147 ())). Qed.

Lemma blk_b7104 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  fkl fcs_idx F0 F ->
  frm0 fc ->
  evt rsegs body_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7140) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfTrunctfdf2 ()) ["Body"] (Mh_0070_blobs2.kr_b_148 ())). Qed.

Lemma blk_b7058 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  fkl fcs_idx F0 F ->
  frm0 fc ->
  evt rsegs body_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7094) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfTrunctfdf2 ()) ["Body"] (Mh_0070_blobs2.kr_b_149 ())). Qed.

End Body.

Theorem trunctfdf2_vff : vff_spec 0xb7094 0.
Proof.
ltac2:(KReplay.run1 (kr_t_WdVfTrunctfdf2 ()) [] (Mh_0070_blobs2.kr_b_150 ())). Qed.

End WdVfTrunctfdf2.
