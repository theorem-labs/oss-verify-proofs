(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Mh_0069_blobs1 Mh_0069_blobs2.
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0069 () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib6VdMath3VDM4hideC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega=RingMicromega5Psatz00I46Stdlib9micromega7EnvRing5PExpr00C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04I46Stdlib9micromega=RingMicromega7Formula00I46Stdlib9micromega5Tauto8GFormula00C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic3and00C46Stdlib9micromega;ZifyClasses3injI45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z7compareC45stdpp9bitvector;definitions:bv_modulusK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes6option02K4ELinuxProcessSemantics5Riscv5Instr5instr0:I4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr03C45stdpp9bitvector;definitions9bv_signedK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega:ZMicromega=Zeval_formulaC46Stdlib9micromega5Tauto7eval_bfK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01I47Corelib4Init9Datatypes4prod00C45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv5Instr5instr06C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3sxbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextK4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv5Instr5instr07C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells6cbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3divC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zK4ELinuxProcessSemantics5Riscv7Prelude4tree02C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem2waC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC46Stdlib5Lists4List9nth_errorI47Corelib4Init5Peano2le00C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:munch_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:wmono_reflC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangec59OSSVerify5KrLib7Mh_00696VaWkDg<sub_mod_stepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_boundC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C46Stdlib5Lists4List>nth_error_NoneC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr3updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr:upd_lengthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3zxbC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr:u8arr_readC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr>u8arr_store_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C79OSSVerify5KrLib2CJ3Lib7Mh_00393MemAsext_extract_byteC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells7cell_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells5csizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393MemAzext_extract_byteC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv3Sem4core01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_1'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6insideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_writeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg9fin1_walkC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge8bv_ltu_ZC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z6ltb_geC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib6VdMath3VDM8land_W64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula05C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega6VarMap4findK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula03C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr5u8arrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5wmonoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK46Stdlib9micromega5Tauto8GFormula06C45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv3Sem4core00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op205K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop05I47Corelib4Init5Logic4True00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem2w0I47Corelib4Init5Logic5False00C46Stdlib5Lists4List6nth_okC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c59OSSVerify5KrLib7Mh_00696VaWkDg4nth3C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz07I46Stdlib9micromega7EnvRing3Pol00K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppK4ELinuxProcessSemantics5Riscv5Instr5instr09C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6shiftrK79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem4sx32C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem:length_le4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC49OSSVerify5KrLib8PropExec5v_sllC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_srliC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_sllC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cell_updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMem8sx32_ztbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC59OSSVerify5KrLib7Mh_00597WdWkMem8ztb_uaddC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg5tk_nzC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_addC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib7Mh_00597WdWkKit<land_W_smallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg8rw1_loopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame7outsideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6sub_fpC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib7SFModel<mod64_land63C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5instr0BC49OSSVerify5KrLib8PropExec5v_mulC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg8ksum_valC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC49OSSVerify5KrLib8PropExec5m_mulC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg9fin2_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg8rw2_loopC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC47Corelib4Init5Logic9False_indC47Corelib4Init5Peano2ltC49OSSVerify5KrLib8PropExec5v_srlC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C46Stdlib5Arith;Compare_dec9le_lt_decI47Corelib4Init6Specif7sumbool00C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge5inr64C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_srlC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_andC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundc59OSSVerify5KrLib7Mh_00696VaWkDg:u8arr_cellC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z:ones_equivC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z:pow_succ_rc59OSSVerify5KrLib7Mh_00696VaWkDg8rw2_walkC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC4ELinuxProcessSemantics5Riscv7Prelude4tsetC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge8bv_eqb_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkKit>land_M32_smallC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge9zr_shiftrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI47Corelib7Numbers7BinNums8positive00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c59OSSVerify5KrLib7Mh_00697VaWkDg23dvkC1?~~~~~~~~~~~~~~~K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom5PExpr00C56Stdlib6ZArith6BinInt1Z6ltb_ltK4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr0;C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_mulhuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_1_rI46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C49OSSVerify5KrLib8PropExec7v_divuwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_subwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5alu32C49OSSVerify5KrLib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7w_divuwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6w_subwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decc59OSSVerify5KrLib7Mh_00696VaWkDg8rw1_walkC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7m_mulhuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:shiftl_0_lC56Stdlib6ZArith6BinInt1Z7add_0_lc59OSSVerify5KrLib7Mh_00696VaWkDg:loop2_walkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkKit=swrap32_smallC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqc59OSSVerify5KrLib7Mh_00697VaWkDg29divuw_valC1?~~~~~~~~~~~~~~~C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK4ELinuxProcessSemantics5Riscv5Instr5mulop06K4ELinuxProcessSemantics5Riscv5Instr5mulop04I46Stdlib;setoid_ring<Ring_polynom3Mon00C45stdpp9bitvector;definitions5bv_eqK79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell01C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02K4ELinuxProcessSemantics5Riscv5Instr5instr01C49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC49OSSVerify5KrLib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDg37dg_postC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8ro_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame9stk_carveC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem:length_le8C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameBro_cells_transportC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr?u8arr_transportC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C45stdpp9bitvector;definitions9bv_concatC49OSSVerify5KrLib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@ro_cells_read_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step9wa_of_varC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5b_luiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_commc59OSSVerify5KrLib7Mh_00697VaWkDg2:kloop_walkC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6ret_pcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;stk_releaseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec7evt_cutC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:shiftl_1_lC59OSSVerify5KrLib6VdMath3VDM;swrap32_oppC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge?zb_shl_shr_landC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3stkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells;cb_split_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cb_splitC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame9stk_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8load_u64C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04C4ELinuxProcessSemantics5Riscv3Sem2w1C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w1_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00695VaWkG6g_postC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMem<rw_cells_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDg37dg_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;ret_pc_evenC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib;setoid_ring<Ring_polynom5PExpr03C56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09K4ELinuxProcessSemantics5Riscv5Instr5instr0QK4ELinuxProcessSemantics5Riscv5Instr5instr0LK46Stdlib;setoid_ring<Ring_polynom5PExpr05K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr08K4ELinuxProcessSemantics5Riscv5Instr5instr0IC4ELinuxProcessSemantics5Riscv3Sem7reg_getC59OSSVerify5KrLib5VaTab3VAT3kcwC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP8fcvt_d_wC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP6fmul_dC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP8fcvt_w_dC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4rgetC59OSSVerify5KrLib5VaTab3VAT8kc_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5VaTab3VAT3s32C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Image>ro_cells_imageC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP9bv_lit_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM<swrap32_lsubC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem7with_pcC4ELinuxProcessSemantics5Riscv3Sem6accrueC4ELinuxProcessSemantics5Riscv3Sem4fsetK4ELinuxProcessSemantics5Riscv3Sem3eff01C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;interp_eff0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lift_resultC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4execC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP<rmode_staticC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP=exec_fcvt_d_wC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP;frm0_accrueC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4fgetC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP6fari_dC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP9rmode_dynC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP;exec_fari_dC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4rsetC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP=exec_fcvt_w_dC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z@div_mul_cancel_lC56Stdlib6ZArith6BinInt1Z9div_add_lC59OSSVerify5KrLib5VaTab3VAT9tabf_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5VaTab3VAT9tabe_readC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_mulC59OSSVerify5KrLib6VdMath3VDM:swrap32_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM;swrap32_subC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?mul_mod_distr_rC56Stdlib6ZArith6BinInt1Z;shiftl_landC56Stdlib6ZArith6BinInt1Z7mod_modC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM4mulrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM<prod32_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z?mul_mod_idemp_rC59OSSVerify5KrLib6VdMath3VDM<land_hi_maskC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC59OSSVerify5KrLib6VdMath3VDM9mulr_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM8mulr_lb1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM9mulr_lb62C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM7mulr_ubC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00695VaWkG:land_W_M32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6mod_eqC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lc59OSSVerify5KrLib7Mh_00695VaWkG7c2_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM:mulr_partsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6VdMath3VDM;mul_machineC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkKit;mulhu_pre32C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP=freg_get_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP>freg_get_otherC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FPCbvmap_set_set_same'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FPBbvmap_set_set_commC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Fpu9fp_of_intC47Corelib4Init9Datatypes3sndC4ELinuxProcessSemantics5Riscv3Fpu;fflags_bitsC56Stdlib6ZArith6BinInt1Z3lorC79OSSVerify5KrLib2CJ3Lib7Mh_00392FP7fari_flC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Fpu9fp_to_intC4ELinuxProcessSemantics5Riscv3Fpu:fmt_doubleK4ELinuxProcessSemantics5Riscv3Fpu5rmode01I4ELinuxProcessSemantics5Riscv3Fpu6fflags00K4ELinuxProcessSemantics5Riscv5Instr6fariop03K4ELinuxProcessSemantics5Riscv3Fpu5rmode04K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty06K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty01K4ELinuxProcessSemantics5Riscv5Instr4ffmt02C59OSSVerify5KrLib5VaTab3VAT5TABFwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5VaTab3VAT5TABEwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5VaTab3VAT6TABF_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5VaTab3VAT6TABE_AC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv3Sem3eff00I4ELinuxProcessSemantics5Riscv3Fpu5rmode00K4ELinuxProcessSemantics5Riscv5Instr5instr0RC49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8mul_commC59OSSVerify5KrLib7Mh_00258WdSfBase=lor_shift_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_1_lc59OSSVerify5KrLib7Mh_00695VaWkG=grisu_c2_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_lorC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr6fmvdir01K4ELinuxProcessSemantics5Riscv5Instr5aluop09K46Stdlib9micromega=RingMicromega5Psatz01c59OSSVerify5KrLib7Mh_00696VaWkGp8dn_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9div_smallc59OSSVerify5KrLib7Mh_00696VaWkGp8lpA_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkGp8lpB_walkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9pow_add_rK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_xoriC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop06c59OSSVerify5KrLib7Mh_00697VaWkDgC4dclsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC<sub_mod_stepC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_Somec59OSSVerify5KrLib7Mh_00697VaWkDgC8dec_byteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC=dcls_set_lastC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC9dcls_lastC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC9fin1_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC8dcls_updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC9fin2_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC4nth3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC5tk_nzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC8rw1_loopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC8ksum_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC8rw2_loopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC:u8arr_cellC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decc59OSSVerify5KrLib7Mh_00697VaWkDgC9dcls_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmul_le_mono_pos_rc59OSSVerify5KrLib7Mh_00697VaWkDgC8rw2_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698VaWkDg2C3dvkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC56Stdlib6ZArith6BinInt1ZBmul_le_mono_nonnegc59OSSVerify5KrLib7Mh_00697VaWkDgC8rw1_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC:loop2_walkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6mod_leC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC56Stdlib6ZArith6BinInt1Z:mul_div_lec59OSSVerify5KrLib7Mh_00698VaWkDg2C9divuw_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698VaWkDg3C7dg_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC8dcls_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698VaWkDg2C:kloop_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkGC6g_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698VaWkDg3C7dg_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkGC:land_W_M32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkGC7c2_tailC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkGC=grisu_c2_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkGpC8dn_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkGpC8lpA_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkGpC8lpB_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697WaWkOut3fj0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697WaWkOut3fj1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697WaWkOut3fj2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697WaWkOut3fj3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697WaWkOut3fj4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697WaWkOut3fj5C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697WaWkOut3fj6C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697WaWkOut3fj7C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697WaWkOut5fileCC1?~~~~~~~~~~~~~~~C49OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan]Tgt_fuzz_msgpack_encoder_asan_loaded_segmentsC1@~~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00697WaWkOut5fjunk00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697WaWkOut6zflagsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtC56Stdlib6ZArith6BinInt1Z3lebC49OSSVerify5KrLib8PropExec6v_sltiC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbc59OSSVerify5KrLib7Mh_00698WaWkFmtE4fstyC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_sltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE>swrap32_addk32C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addwC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge7zr_lxorC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr6u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00648WaWkFmtB8limbs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr<u32arr_boundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE;stripE_walkC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9alu_sltiuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_sltiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_sltC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6w_addwC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib7Mh_00597WdWkMemAswrap32_landW_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7lor_0_lC46Stdlib4Bool4Bool<andb_false_rc59OSSVerify5KrLib7Mh_00698WaWkFmtE6lorW_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC69OSSVerify5KrLib2CJ3Lib7SFModel8land_W64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE4notWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE7sgn_keyC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge9v_slt_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge:v_slti_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;v_sltiu_b2zC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204K46Stdlib9micromega=RingMicromega3Op206K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5instr0<C49OSSVerify5KrLib8PropExec6v_sraiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC49OSSVerify5KrLib8PropExec8alu_sraiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z8min_specC69OSSVerify5KrLib2CJ3Lib7SFModel;signed_of_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8le_min_lC56Stdlib6ZArith6BinInt1Z;min_glb_iffC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z8le_min_rC56Stdlib6ZArith6BinInt1Z5min_rC56Stdlib6ZArith6BinInt1Z5min_lc59OSSVerify5KrLib7Mh_00698WaWkFmtE9ztb_landWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE:max0_idiomC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtEClandW_sub_add_innerC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE6ztb_9kC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_slliwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_srliwC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u32arr_readC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7w_slliwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7w_srliwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE;tzloop_walkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00648WaWkFmtB;sx32_smallwC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula09K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C46Stdlib5Lists4List=firstn_firstnC47Corelib4Init3Nat3minC47Corelib4Init3Nat3subK79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3absC49OSSVerify5KrLib8PropExec7v_sraiwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_xorC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_wfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem5wr_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells;cells_bytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC49OSSVerify5KrLib8PropExec7w_sraiwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_xorC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_oriC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8abs_specC49OSSVerify5KrLib8PropExec7alu_oriC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_divC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697WaWkOut=cells_reshapeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE9sign_formC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE6isdigbC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01c59OSSVerify5KrLib7Mh_00698WaWkFmtE5lor48C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE:digit_formC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE:div10_formC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE9abs_idiomC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List@firstn_length_leK47Corelib5Lists7ListDef6Forall02".
Module VaWkDg.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import VdMath.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VaWkDg () := "C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbI4ELinuxProcessSemantics5Riscv7Prelude4tree00C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9alu_sltiuC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK4ELinuxProcessSemantics5Riscv5Instr5instr0:C49OSSVerify5KrLib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK4ELinuxProcessSemantics5Riscv5Instr5instr03C49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_xoriC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_lorC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;v_sltiu_b2zC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_subC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop05C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5instr0BC56Stdlib6ZArith6BinInt1Z3mulC49OSSVerify5KrLib8PropExec5v_mulC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5m_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divK4ELinuxProcessSemantics5Riscv5Instr5mulop01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC46Stdlib6ZArith4ZdivBZminus_mod_idemp_rK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib6VdMath3VDM4hideC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:munch_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:wmono_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_boundC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_NoneC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem2waC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr:u8arr_readC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr>u8arr_store_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rc59OSSVerify5KrLib7Mh_00696VaWkDg9fin2_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3sxbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells6cbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393MemAsext_extract_byteC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells7cell_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells5csizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3zxbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC79OSSVerify5KrLib2CJ3Lib7Mh_00393MemAzext_extract_byteC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_1'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u8arr_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6insideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr3updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr:upd_lengthC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge8bv_ltu_ZC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC45stdpp9bitvector;definitions@Z_to_bv_unsignedC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_transC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr5u8arrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC45stdpp9bitvector;definitions:bv_extractC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okK4ELinuxProcessSemantics5Riscv5Instr5msize01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6shiftlK47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init5Logic4True01C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8bytes_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem5wr_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr<nth_error_ltC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC47Corelib4Init5Logic3notC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_wfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells;cells_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3mrdC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC46Stdlib9micromega;ZifyClasses6eq_iffC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith6BinInt1Z3divC47Corelib7Classes?RelationClasses=eq_TransitiveC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z9div_add_lC56Stdlib6ZArith6BinInt1Z8mul_commC46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2Zrc59OSSVerify5KrLib7Mh_00696VaWkDg4nth3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMem8ztb_uaddC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem4sx32C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib7Mh_00597WdWkMem8sx32_ztbC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Asan.M.loaded_segments (only parsing).

Ltac brs := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let B := fresh "B" in destruct c eqn:B end.

(* [comment removed for export] *)
Lemma fin1_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => exists (res : Z) a1' a2' t2',
      ms' = MS (mkR ra sp gp tp t0 t1 t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0xbcdec) fc None m (seg_rom rsegs) /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcd64) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg ()) [] (Mh_0069_blobs1.kr_b_001 ())). Qed.

Lemma fin2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => exists (res : Z) a1' a2' a4',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0xbcdec) fc None m (seg_rom rsegs) /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcd9c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg ()) [] (Mh_0069_blobs1.kr_b_002 ())). Qed.

Ltac no_vars c := match c with context [?x] => is_var x; fail 2 "open term" | _ => idtac end.
(* [comment removed for export] *)
Ltac cbr := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  no_vars c; let v := eval vm_compute in c in change c with v; cbv iota end.
Ltac fix_sbw :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?c)) _) => change (Z_to_le_bytes 1 c) with [Z_to_bv 8 c]
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => change (le1 w) with [Z_to_bv 8 (bv_unsigned w)]
  end.
Ltac gfalse tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let BR := fresh "BR" in assert (BR : c = false) by tac; rewrite BR; cbv iota; clear BR end.

Open Scope Z_scope.
Lemma sub_mod_step D r tk : 0 <= D < 2 ^ 64 -> 0 <= r < 2 ^ 64 -> 1 <= tk <= (D - r) mod 2 ^ 64 ->
  (D - (r + tk) mod 2 ^ 64) mod 2 ^ 64 = (D - r) mod 2 ^ 64 - tk.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg ()) [] (Mh_0069_blobs1.kr_b_003 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma rw1_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len shp : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) < 2 ^ 63)%Z ->
  rw_cells rsegs m shp [CB 1 [Z_to_bv 8 0]] -> (shp + 1 <= buf \/ buf + Z.of_nat (length bs) <= shp)%Z -> (0 <= shp)%Z -> (shp + 1 < 2 ^ 63)%Z ->
  ((bv_unsigned a3 - bv_unsigned s5) mod 2 ^ 64 <= Z.of_nat n)%Z ->
  (1 <= bv_unsigned a1 <= (bv_unsigned a3 - bv_unsigned s5) mod 2 ^ 64)%Z ->
  a0 = Z_to_bv 64 (buf + (len - 1)) -> t0 = Z_to_bv 64 shp ->
  evt rsegs (fun ms' => exists (res : Z) a1' a2' a4' a6' a7' t2' t3' s5' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3 a4' a5 a6' a7' s2 s3 s4 s5' s6 s7 s8 s9 s10 s11 t3' t4 t5 t6) F
               (Z_to_bv 64 0xbcdec) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' shp [CB 1 [Z_to_bv 8 0]] /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcbb8) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_004 ())). Qed.

(* [comment removed for export] *)
Lemma rw2_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len shp : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) < 2 ^ 63)%Z ->
  rw_cells rsegs m shp [CB 1 [Z_to_bv 8 0]] -> (shp + 1 <= buf \/ buf + Z.of_nat (length bs) <= shp)%Z -> (0 <= shp)%Z -> (shp + 1 < 2 ^ 63)%Z ->
  (bv_unsigned s0 < Z.of_nat n)%Z -> (1 <= bv_unsigned a4)%Z ->
  a0 = Z_to_bv 64 (buf + (len - 1)) -> t0 = Z_to_bv 64 shp ->
  evt rsegs (fun ms' => exists (res : Z) a1' a2' a4' a5' a7' t3' t5' t6' s0' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 (Z_to_bv 64 res) a1' a2' a3 a4' a5' a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5' t6') F
               (Z_to_bv 64 0xbcdec) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' shp [CB 1 [Z_to_bv 8 0]] /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcd10) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg ()) [] (Mh_0069_blobs1.kr_b_005 ())). Qed.

Ltac setreg2 n e t := let v := getreg n in replace v with e by (symmetry; t).
Open Scope Z_scope.
Lemma land7_0 k : k mod 8 = 0 -> Z.land k 7 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg ()) [] (Mh_0069_blobs1.kr_b_006 ())). Qed.
Lemma tk_nz dv sh : dv = 100 \/ dv = 10 \/ dv = 1 -> 56 <= sh <= 59 -> 1 <= bv_unsigned (Z_to_bv 64 (Z.shiftl dv (Z.land sh 63))).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg ()) [] (Mh_0069_blobs1.kr_b_007 ())). Qed.
Lemma tk_nz2 dv sh : dv = 100 \/ dv = 10 \/ dv = 1 -> 56 <= sh <= 59 -> 1 <= bv_unsigned (Z_to_bv 64 (Z.shiftl dv sh)).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg ()) [] (Mh_0069_blobs1.kr_b_008 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma u8arr_cell m A bs (i : Z) b :
  u8arr rsegs m A bs -> nth_error bs (Z.to_nat i) = Some b -> (0 <= i)%Z -> rw_cells rsegs m (A + i)%Z [CB 1 [b]].
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg ()) [] (Mh_0069_blobs1.kr_b_009 ())). Qed.
Open Scope Z_scope.
Lemma div8_split b l : b mod 8 = 0 -> (b + l) / 8 = b / 8 + l / 8.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg ()) [] (Mh_0069_blobs1.kr_b_010 ())). Qed.
Lemma nth3 {T} (b : T) i : (i < 3)%nat -> nth_error [b; b; b] i = Some b.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg ()) [] (Mh_0069_blobs1.kr_b_011 ())). Qed.
Close Scope Z_scope.

Open Scope Z_scope.
Lemma ksum_val k0 d : - 2 ^ 31 <= k0 < 2 ^ 31 -> Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 k0)) + d) = Z_to_bv 64 (k0 + d).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg ()) [] (Mh_0069_blobs1.kr_b_012 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma rw1_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 kap dv sh shl : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) <= 2 ^ 47)%Z -> (Z.of_nat (length bs) < 2 ^ 31)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + Z.of_nat (length bs) <= kp)%Z -> (lenp + 4 <= buf \/ buf + Z.of_nat (length bs) <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z ->
  (buf + Z.of_nat (length bs) <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m shl [CB 1 [Z_to_bv 8 0]] -> (shl = 2147450880 + lenp / 8)%Z ->
  rw_cells rsegs m (2147450880 + buf / 8 + (len - 1) / 8) [CB 1 [Z_to_bv 8 0]] ->
  (bv_unsigned s5 < bv_unsigned a3)%Z -> (56 <= sh <= 59)%Z -> (dv = 100 \/ dv = 10 \/ dv = 1)%Z -> (1 <= kap <= 3)%Z -> (- 2 ^ 20 <= k0 <= 2 ^ 20)%Z ->
  a0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> s1 = Z_to_bv 64 dv -> t4 = Z_to_bv 64 sh -> s0 = Z_to_bv 64 (kap + 1) ->
  t0 = Z_to_bv 64 2147450880 -> t1 = Z_to_bv 64 shl ->
  evt rsegs (fun ms' => exists (res : Z) t0' t3' t5' a1' a2' a4' a5' a6' a7' t2' s5' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1 t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3 a4' a5' a6' a7' s2 s3 s4 s5' s6 s7 s8 s9 s10 s11 t3' t4 t5' t6) F
               (Z_to_bv 64 0xbcdec) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs)); (kp, kp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + (kap - 1)))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)]
      /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcb64) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_013 ())). Qed.

(* [comment removed for export] *)
Lemma rw2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 kap shl : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) <= 2 ^ 47)%Z -> (Z.of_nat (length bs) < 2 ^ 31)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + Z.of_nat (length bs) <= kp)%Z -> (lenp + 4 <= buf \/ buf + Z.of_nat (length bs) <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z ->
  (buf + Z.of_nat (length bs) <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m shl [CB 1 [Z_to_bv 8 0]] -> (shl = 2147450880 + lenp / 8)%Z ->
  rw_cells rsegs m (2147450880 + buf / 8 + (len - 1) / 8) [CB 1 [Z_to_bv 8 0]] ->
  (1 <= bv_unsigned a4)%Z -> (- 2 ^ 20 <= kap <= 0)%Z -> (- 2 ^ 20 <= k0 <= 2 ^ 20)%Z ->
  a0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> s1 = Z_to_bv 64 kap -> t0 = Z_to_bv 64 2147450880 -> t1 = Z_to_bv 64 shl ->
  evt rsegs (fun ms' => exists (res : Z) t0' t1' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6' s0' s1' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 s0' s1' (Z_to_bv 64 res) a1' a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (Z_to_bv 64 0xbcdec) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs)); (kp, kp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + kap))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)]
      /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcc9c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_014 ())). Qed.

(* [comment removed for export] *)
Lemma loop2_walk : forall (k n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 sh Dl p2 shl : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m shl [CB 1 [Z_to_bv 8 0]] -> (shl = 2147450880 + lenp / 8)%Z ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  (n + k = 18)%nat -> (10 ^ Z.of_nat n <= Dl)%Z -> (Dl <= p2 < 2 ^ sh)%Z -> (56 <= sh <= 59)%Z -> (1 <= len <= 3 + Z.of_nat n)%Z -> (- 2 ^ 19 <= k0 <= 2 ^ 19)%Z ->
  a0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> s1 = Z_to_bv 64 (- Z.of_nat n) -> t4 = Z_to_bv 64 sh -> s2 = Z_to_bv 64 10 ->
  a3 = Z_to_bv 64 Dl -> t3 = Z_to_bv 64 p2 -> t6 = Z_to_bv 64 (2 ^ sh - 1) -> a4 = Z_to_bv 64 (2 ^ sh) -> t5 = Z_to_bv 64 4294967295 ->
  t0 = Z_to_bv 64 2147450880 -> t1 = Z_to_bv 64 shl ->
  evt rsegs (fun ms' => exists (res len' dk : Z) t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s3' s4' t3' t4' t5' t6' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (Z_to_bv 64 0xbcdec) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + dk))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-18 <= dk <= 2)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcc0c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_015 ())). Qed.

End VaWkDg.
Module VaWkDg2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VaWkDg2 () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib6VdMath3VDM4hideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg4nth3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions8bv_swrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_posC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00597WdWkKit=swrap32_smallC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_divuwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Asan.M.loaded_segments (only parsing).

Open Scope Z_scope.
Definition dvk (j : nat) : Z := match j with 3%nat => 100 | 2%nat => 10 | _ => 1 end.
Lemma divuw_val (x d : Z) : 0 <= x < 2 ^ 31 -> 0 < d < 2 ^ 31 -> v_divuw (Z_to_bv 64 x) (Z_to_bv 64 d) = Z_to_bv 64 (x / d).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg2 ()) [] (Mh_0069_blobs1.kr_b_016 ())). Qed.
Close Scope Z_scope.
(* [comment removed for export] *)
Ltac hid H := let T := type of H in change (VDM.hide T) in H.

(* [comment removed for export] *)
Lemma kloop_walk : forall (j : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 sh Dl p1 Wp1 shl : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m shl [CB 1 [Z_to_bv 8 0]] -> (shl = 2147450880 + lenp / 8)%Z ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  (1 <= j <= 3)%nat -> (56 <= sh <= 59)%Z -> (1 <= Dl <= Wp1)%Z -> (2 ^ sh <= Wp1 < 2 ^ 64)%Z -> (0 <= p1 < 10 * dvk j)%Z -> (0 <= len <= 3 - Z.of_nat j)%Z ->
  (len = 0 -> p1 = Wp1 / 2 ^ sh)%Z -> (- 2 ^ 19 <= k0 <= 2 ^ 19)%Z ->
  a0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> s2 = Z_to_bv 64 1 -> t4 = Z_to_bv 64 sh ->
  a3 = Z_to_bv 64 Dl -> t3 = Z_to_bv 64 (Wp1 mod 2 ^ sh) -> t6 = Z_to_bv 64 (2 ^ sh - 1) -> a4 = Z_to_bv 64 (2 ^ sh) ->
  s3 = Z_to_bv 64 p1 -> s1 = Z_to_bv 64 (dvk j) -> s0 = Z_to_bv 64 (Z.of_nat j + 1) -> s4 = Z_to_bv 64 0xcccccccd00000000 -> t5 = Z_to_bv 64 4294967295 ->
  t0 = Z_to_bv 64 2147450880 -> t1 = Z_to_bv 64 shl ->
  evt rsegs (fun ms' => exists (res len' dk : Z) t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (Z_to_bv 64 0xbcdec) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + dk))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-18 <= dk <= 2)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcacc) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_017 ())). Qed.

End VaWkDg2.
Module VaWkDg3.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg2.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Asan.M.loaded_segments (only parsing).

Definition dg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo buf kp lenp k0 : Z) : machine_state -> Prop :=
  fun ms' => exists (res len' dk : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (bv_unsigned sp) [C8 (Z_to_bv 64 kp)] /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + dk))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-18 <= dk <= 2)%Z.

(* [comment removed for export] *)
Lemma dg_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp k0 Wm W Wp E e1 e3 e5 : Z) (bs lb : list byte),
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> (lo + 80 <= bv_unsigned sp)%Z -> (bv_unsigned sp + 8 <= 2 ^ 47)%Z -> (0x6b6000 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 kp)] ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp + 8 <= kp \/ kp + 4 <= lo)%Z -> (bv_unsigned sp + 8 <= lenp \/ lenp + 4 <= lo)%Z -> (bv_unsigned sp + 8 <= buf \/ buf + 22 <= lo)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z ->
  (bv_unsigned sp + 8 <= 2147446784 \/ 17594333495296 <= lo)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  ro_cells rsegs m 0x156d98 [C8 (Z_to_bv 64 0x15fa78)] -> ro_cells rsegs m 0x15fa78 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m (2147450880 + lenp / 8) [CB 1 [Z_to_bv 8 0]] ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  (1 <= Wm <= Wp)%Z -> (W <= Wp)%Z -> (0 <= W)%Z -> (2 ^ 59 <= Wp <= 2 ^ 64 - 2)%Z -> (-59 <= E <= -56)%Z -> (- 2 ^ 19 <= k0 <= 2 ^ 19)%Z ->
  (0 <= e1 < 2 ^ 64)%Z -> (0 <= e3 < 2 ^ 64)%Z -> (0 <= e5 < 2 ^ 64)%Z -> bv_swrap 32 e1 = E -> bv_swrap 32 e3 = E -> bv_swrap 32 e5 = E ->
  a0 = Z_to_bv 64 Wm -> a1 = Z_to_bv 64 e1 -> a2 = Z_to_bv 64 W -> a3 = Z_to_bv 64 e3 -> a4 = Z_to_bv 64 Wp -> a5 = Z_to_bv 64 e5 ->
  a6 = Z_to_bv 64 buf -> a7 = Z_to_bv 64 lenp ->
  evt rsegs (dg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo buf kp lenp k0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbca0c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_018 ())). Qed.

End VaWkDg3.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath VaTab.
Module VaWkG.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath VaTab. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VaTab OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg3.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VaWkG () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib6VdMath3VDM4hideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg4nth3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC56Stdlib6ZArith6BinInt1Z4onesK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z9land_onesC59OSSVerify5KrLib6VdMath3VDM8land_W64C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Asan.M.loaded_segments (only parsing).

Open Scope Z_scope.
Lemma land_W_M32 x : Z.land (Z.land x 18446744073709551615) 4294967295 = x mod 2 ^ 32.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkG ()) [] (Mh_0069_blobs1.kr_b_019 ())). Qed.
Close Scope Z_scope.

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
Lemma c2_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (spz lo buf kp lenp mk Wm W Wp E e1 : Z) (junk8 bs kb lb : list byte) (o_ra o_s0 o_s1 o_s2 o_s3 o_s4 o_s5 o_s6 o_s7 : word),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo spz -> (lo + 80 <= spz)%Z -> (spz + 80 <= 2 ^ 47)%Z -> (0x6b6000 <= lo)%Z -> (bv_unsigned o_ra mod 2 = 0)%Z ->
  rw_cells rsegs m spz [CB 8 junk8; C8 o_s7; C8 o_s6; C8 o_s5; C8 o_s4; C8 o_s3; C8 o_s2; C8 o_s1; C8 o_s0; C8 o_ra] ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (spz + 80 <= kp \/ kp + 4 <= lo)%Z -> (spz + 80 <= lenp \/ lenp + 4 <= lo)%Z -> (spz + 80 <= buf \/ buf + 22 <= lo)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z -> (0x6b6000 <= kp)%Z ->
  (spz + 80 <= 2147446784 \/ 17594333495296 <= lo)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  ro_cells rsegs m 0x156d98 [C8 (Z_to_bv 64 0x15fa78)] -> ro_cells rsegs m 0x15fa78 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m (2147450880 + lenp / 8) [CB 1 [Z_to_bv 8 0]] ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  (-307 <= mk <= 325)%Z -> (1 <= Wm <= W)%Z -> (W <= Wp)%Z -> (2 ^ 62 <= Wp <= 2 ^ 64 - 2)%Z -> (-59 <= E <= -56)%Z -> (0 <= e1 < 2 ^ 32)%Z -> bv_swrap 32 e1 = E ->
  a0 = Z_to_bv 64 Wm -> a1 = Z_to_bv 64 e1 -> a2 = Z_to_bv 64 kp -> a3 = Z_to_bv 64 e1 -> a4 = Z_to_bv 64 Wp -> a5 = Z_to_bv 64 W -> t2 = Z_to_bv 64 (- mk) ->
  s0 = Z_to_bv 64 lenp -> s1 = Z_to_bv 64 buf -> s2 = Z_to_bv 64 2147450880 -> sp = Z_to_bv 64 spz ->
  evt rsegs (g_post o_ra (Z_to_bv 64 (spz + 80)) gp tp o_s0 o_s1 o_s2 o_s3 o_s4 o_s5 o_s6 o_s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbc0e0) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_020 ())). Qed.

(* [comment removed for export] *)
Lemma grisu_c2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (spz lo buf kp lenp mi mie pe P Wn sh : Z) (junk8 bs kb lb zf ze : list byte) (o_ra o_s0 o_s1 o_s2 o_s3 o_s4 o_s5 o_s6 o_s7 : word),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo spz -> (lo + 80 <= spz)%Z -> (spz + 80 <= 2 ^ 47)%Z -> (0x6b6000 <= lo)%Z -> (bv_unsigned o_ra mod 2 = 0)%Z ->
  rw_cells rsegs m spz [CB 8 junk8; C8 o_s7; C8 o_s6; C8 o_s5; C8 o_s4; C8 o_s3; C8 o_s2; C8 o_s1; C8 o_s0; C8 o_ra] ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (spz + 80 <= kp \/ kp + 4 <= lo)%Z -> (spz + 80 <= lenp \/ lenp + 4 <= lo)%Z -> (spz + 80 <= buf \/ buf + 22 <= lo)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z -> (0x6b6000 <= kp)%Z ->
  (spz + 80 <= 2147446784 \/ 17594333495296 <= lo)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  ro_cells rsegs m 0x156d98 [C8 (Z_to_bv 64 0x15fa78)] -> ro_cells rsegs m 0x15fa78 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m (2147450880 + lenp / 8) [CB 1 [Z_to_bv 8 0]] ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  u8arr rsegs m (2147450880 + 18316) zf -> length zf = 687%nat -> (forall i, (i < 687)%nat -> nth_error zf i = Some (Z_to_bv 8 0)) ->
  u8arr rsegs m (2147450880 + 19172) ze -> length ze = 343%nat -> (forall i, (i < 343)%nat -> nth_error ze i = Some (Z_to_bv 8 0)) ->
  (1 <= mi)%Z -> (sh = mie - pe + 10)%Z -> (9 <= sh <= 62)%Z -> (mi * 2 ^ sh <= Wn * 2 ^ 11)%Z -> (Wn * 2 ^ 11 <= P * 2 ^ 10)%Z -> (2 ^ 63 <= P * 2 ^ 10 < 2 ^ 64)%Z ->
  (-1021 <= -50 - pe <= 1077)%Z -> (-2000 <= mie <= 2000)%Z -> (0 <= Wn)%Z -> (0 <= P)%Z ->
  a4 = Z_to_bv 64 (pe + 1) -> a2 = Z_to_bv 64 kp -> a3 = Z_to_bv 64 mie -> t1 = Z_to_bv 64 pe -> a6 = Z_to_bv 64 Wn -> a7 = Z_to_bv 64 mi ->
  t0 = Z_to_bv 64 P -> s0 = Z_to_bv 64 lenp -> s1 = Z_to_bv 64 buf -> s2 = Z_to_bv 64 2147450880 -> sp = Z_to_bv 64 spz ->
  evt rsegs (g_post o_ra (Z_to_bv 64 (spz + 80)) gp tp o_s0 o_s1 o_s2 o_s3 o_s4 o_s5 o_s6 o_s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbbf20) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_021 ())). Qed.

End VaWkG.
Module VaWkGp.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath VaTab. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VaTab OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkG.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VaWkGp () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib6VdMath3VDM4hideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg4nth3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z:pow_succ_rK4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec7alu_andC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09I4ELinuxProcessSemantics5Riscv7Prelude4tree00C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC49OSSVerify5KrLib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr08K47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib6VdMath3VDM<land_pow2_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2ex01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01C59OSSVerify5KrLib6VdMath3VDM<land_pow2_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz01I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega6VarMap1t03C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge=bv_lts_zero_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtK4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C56Stdlib6ZArith6BinInt1Z9log2_specC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rK46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05C56Stdlib6ZArith4Znat5Z2Nat2idC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib5Lists4List9nth_errorC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP4frm0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics5Riscv3Sem7reg_getC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00C47Corelib4Init9Datatypes6lengthK79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8ro_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC47Corelib4Init5Peano2ltc59OSSVerify5KrLib7Mh_00695VaWkG6g_postC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc59OSSVerify5KrLib7Mh_00696VaWkGp<grisu_d_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkGp<grisu_n_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr5u8arrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Asan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
Lemma lpA_walk : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (X e : Z),
  (1 <= n)%nat -> (2 ^ 53 <= X * 2 ^ Z.of_nat n < 2 ^ 54)%Z -> (0 <= X)%Z ->
  a5 = Z_to_bv 64 4503599627370496 -> t0 = Z_to_bv 64 X -> t1 = Z_to_bv 64 e ->
  evt rsegs (fun ms' => exists a4',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (X * 2 ^ Z.of_nat n)) (Z_to_bv 64 (e - Z.of_nat n)) t2 s0 s1 a0 a1 a2 a3 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0xbbedc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbbecc) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkGp ()) [] (Mh_0069_blobs1.kr_b_022 ())). Qed.

(* [comment removed for export] *)
Lemma lpB_walk : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (Y e : Z),
  (1 <= n)%nat -> (2 ^ 52 <= Y * 2 ^ Z.of_nat n < 2 ^ 53)%Z -> (0 <= Y)%Z ->
  a6 = Z_to_bv 64 Y -> a4 = Z_to_bv 64 e ->
  evt rsegs (fun ms' => exists a5',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (e - Z.of_nat n)) a5' (Z_to_bv 64 (Y * 2 ^ Z.of_nat n)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0xbbef0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbbee0) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkGp ()) [] (Mh_0069_blobs1.kr_b_023 ())). Qed.

(* [comment removed for export] *)
Lemma grisu_n_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp u : Z) (bs kb lb zf ze : list byte),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo (bv_unsigned sp) -> (lo + 160 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= 2 ^ 47)%Z -> (0x6b6000 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (forall r, bv_unsigned r = 10%Z -> reg_get F r = Z_to_bv 64 u) -> (2 ^ 52 <= u < 2 ^ 63)%Z ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp <= kp \/ kp + 4 <= lo)%Z -> (bv_unsigned sp <= lenp \/ lenp + 4 <= lo)%Z -> (bv_unsigned sp <= buf \/ buf + 22 <= lo)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z -> (0x6b6000 <= kp)%Z ->
  (bv_unsigned sp <= 2147446784 \/ 17594333495296 <= lo)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  ro_cells rsegs m 0x156d98 [C8 (Z_to_bv 64 0x15fa78)] -> ro_cells rsegs m 0x15fa78 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m (2147450880 + lenp / 8) [CB 1 [Z_to_bv 8 0]] ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  u8arr rsegs m (2147450880 + 18316) zf -> length zf = 687%nat -> (forall i, (i < 687)%nat -> nth_error zf i = Some (Z_to_bv 8 0)) ->
  u8arr rsegs m (2147450880 + 19172) ze -> length ze = 343%nat -> (forall i, (i < 343)%nat -> nth_error ze i = Some (Z_to_bv 8 0)) ->
  a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 lenp -> a2 = Z_to_bv 64 kp ->
  evt rsegs (g_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbbe40) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_024 ())). Qed.

Open Scope Z_scope.
Lemma dn_facts f : 1 <= f < 2 ^ 52 -> exists n : nat, (1 <= n <= 52)%nat /\ 2 ^ 52 <= f * 2 ^ Z.of_nat n < 2 ^ 53 /\ 2 ^ 53 <= (2 * f + 1) * 2 ^ Z.of_nat n < 2 ^ 54.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkGp ()) [] (Mh_0069_blobs1.kr_b_025 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma grisu_d_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp u : Z) (bs kb lb zf ze : list byte),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo (bv_unsigned sp) -> (lo + 160 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= 2 ^ 47)%Z -> (0x6b6000 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (forall r, bv_unsigned r = 10%Z -> reg_get F r = Z_to_bv 64 u) -> (1 <= u < 2 ^ 52)%Z ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp <= kp \/ kp + 4 <= lo)%Z -> (bv_unsigned sp <= lenp \/ lenp + 4 <= lo)%Z -> (bv_unsigned sp <= buf \/ buf + 22 <= lo)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z -> (0x6b6000 <= kp)%Z ->
  (bv_unsigned sp <= 2147446784 \/ 17594333495296 <= lo)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  ro_cells rsegs m 0x156d98 [C8 (Z_to_bv 64 0x15fa78)] -> ro_cells rsegs m 0x15fa78 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m (2147450880 + lenp / 8) [CB 1 [Z_to_bv 8 0]] ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  u8arr rsegs m (2147450880 + 18316) zf -> length zf = 687%nat -> (forall i, (i < 687)%nat -> nth_error zf i = Some (Z_to_bv 8 0)) ->
  u8arr rsegs m (2147450880 + 19172) ze -> length ze = 343%nat -> (forall i, (i < 343)%nat -> nth_error ze i = Some (Z_to_bv 8 0)) ->
  a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 lenp -> a2 = Z_to_bv 64 kp ->
  evt rsegs (g_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbbe40) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_026 ())). Qed.

(* [comment removed for export] *)
Theorem grisu3_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp u : Z) (bs kb lb zf ze : list byte),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo (bv_unsigned sp) -> (lo + 160 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= 2 ^ 47)%Z -> (0x6b6000 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (forall r, bv_unsigned r = 10%Z -> reg_get F r = Z_to_bv 64 u) -> (1 <= u < 2 ^ 63)%Z ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp <= kp \/ kp + 4 <= lo)%Z -> (bv_unsigned sp <= lenp \/ lenp + 4 <= lo)%Z -> (bv_unsigned sp <= buf \/ buf + 22 <= lo)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z -> (0x6b6000 <= kp)%Z ->
  (bv_unsigned sp <= 2147446784 \/ 17594333495296 <= lo)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  ro_cells rsegs m 0x156d98 [C8 (Z_to_bv 64 0x15fa78)] -> ro_cells rsegs m 0x15fa78 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m (2147450880 + lenp / 8) [CB 1 [Z_to_bv 8 0]] ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  u8arr rsegs m (2147450880 + 18316) zf -> length zf = 687%nat -> (forall i, (i < 687)%nat -> nth_error zf i = Some (Z_to_bv 8 0)) ->
  u8arr rsegs m (2147450880 + 19172) ze -> length ze = 343%nat -> (forall i, (i < 343)%nat -> nth_error ze i = Some (Z_to_bv 8 0)) ->
  a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 lenp -> a2 = Z_to_bv 64 kp ->
  evt rsegs (g_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbbe40) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkGp ()) [] (Mh_0069_blobs1.kr_b_027 ())). Qed.

End VaWkGp.
Module VaWkDgC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import VdMath.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VaWkDgC () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib6VdMath3VDM4hideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg4nth3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbI4ELinuxProcessSemantics5Riscv7Prelude4tree00C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9alu_sltiuC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK4ELinuxProcessSemantics5Riscv5Instr5instr0:C49OSSVerify5KrLib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK4ELinuxProcessSemantics5Riscv5Instr5instr03C49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6alu_orC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8alu_xoriC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_lorC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge:v_sltu_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge;v_sltiu_b2zC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_subC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop05C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC46Stdlib6ZArith4ZdivBZminus_mod_idemp_rK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib5Lists4List9nth_errorC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc59OSSVerify5KrLib7Mh_00697VaWkDgC4dclsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Nat2Z6inj_leC79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr3updC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphK46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC47Corelib4Init9Datatypes6lengthc59OSSVerify5KrLib7Mh_00697VaWkDgC8dcls_updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrBnth_error_upd_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkDgC9dcls_lastC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6shiftlK47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init5Logic4True01C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr5u8arrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8bytes_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem5wr_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr<nth_error_ltC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_wfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells;cells_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C46Stdlib9micromega;ZifyClasses3injC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem2waC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3mrdC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC46Stdlib9micromega;ZifyClasses6eq_iffK79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC46Stdlib9micromega;ZifyClasses6mkapp2I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC47Corelib7Classes?RelationClasses=eq_TransitiveC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z9div_add_lC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrC56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib7Mh_00697VaWkDgC4nth3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00597WdWkMem8ztb_uaddC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem4sx32C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib7Mh_00597WdWkMem8sx32_ztbC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Asan.M.loaded_segments (only parsing).

Ltac brs := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let B := fresh "B" in destruct c eqn:B end.

(* [comment removed for export] *)
Lemma fin1_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => exists (res : Z) a1' a2' t2',
      ms' = MS (mkR ra sp gp tp t0 t1 t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0xbcdec) fc None m (seg_rom rsegs) /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcd64) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_028 ())). Qed.

Lemma fin2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => exists (res : Z) a1' a2' a4',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0xbcdec) fc None m (seg_rom rsegs) /\ (res = 0 \/ res = 1)%Z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcd9c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_029 ())). Qed.

Ltac no_vars c := match c with context [?x] => is_var x; fail 2 "open term" | _ => idtac end.
(* [comment removed for export] *)
Ltac cbr := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  no_vars c; let v := eval vm_compute in c in change c with v; cbv iota end.
Ltac fix_sbw :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?c)) _) => change (Z_to_le_bytes 1 c) with [Z_to_bv 8 c]
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => change (le1 w) with [Z_to_bv 8 (bv_unsigned w)]
  end.
Ltac gfalse tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let BR := fresh "BR" in assert (BR : c = false) by tac; rewrite BR; cbv iota; clear BR end.

Open Scope Z_scope.
Lemma sub_mod_step D r tk : 0 <= D < 2 ^ 64 -> 0 <= r < 2 ^ 64 -> 1 <= tk <= (D - r) mod 2 ^ 64 ->
  (D - (r + tk) mod 2 ^ 64) mod 2 ^ 64 = (D - r) mod 2 ^ 64 - tk.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_030 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Definition dcls (bs : list byte) (n : nat) : Prop := forall j, (j < n)%nat -> exists b, nth_error bs j = Some b /\ (46 <= bv_unsigned b <= 57)%Z.
Lemma dcls_nil bs : dcls bs 0.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_031 ())). Qed.
Lemma dcls_mono bs n n' : dcls bs n -> (n' <= n)%nat -> dcls bs n'.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_032 ())). Qed.
Lemma dcls_upd bs n i b : dcls bs n -> (n <= i)%nat -> dcls (upd bs i b) n.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_033 ())). Qed.
Lemma dcls_last bs len b : dcls bs (Z.to_nat (len - 1)) -> (1 <= len)%Z -> nth_error bs (Z.to_nat (len - 1)) = Some b -> (46 <= bv_unsigned b <= 57)%Z -> dcls bs (Z.to_nat len).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_034 ())). Qed.
Lemma dcls_set_last bs len b : dcls bs (Z.to_nat (len - 1)) -> (1 <= len)%Z -> (Z.to_nat (len - 1) < length bs)%nat -> (46 <= bv_unsigned b <= 57)%Z ->
  dcls (upd bs (Z.to_nat (len - 1)) b) (Z.to_nat len).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_035 ())). Qed.
Lemma dec_byte (b : byte) : (1 <= bv_unsigned b)%Z -> bv_unsigned (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b + -1)))) = (bv_unsigned b - 1)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_036 ())). Qed.

(* [comment removed for export] *)
Lemma rw1_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len shp : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) < 2 ^ 63)%Z ->
  rw_cells rsegs m shp [CB 1 [Z_to_bv 8 0]] -> (shp + 1 <= buf \/ buf + Z.of_nat (length bs) <= shp)%Z -> (0 <= shp)%Z -> (shp + 1 < 2 ^ 63)%Z ->
  ((bv_unsigned a3 - bv_unsigned s5) mod 2 ^ 64 <= Z.of_nat n)%Z ->
  (1 <= bv_unsigned a1 <= (bv_unsigned a3 - bv_unsigned s5) mod 2 ^ 64)%Z ->
  a0 = Z_to_bv 64 (buf + (len - 1)) -> t0 = Z_to_bv 64 shp ->
  dcls bs (Z.to_nat (len - 1)) ->
  (exists b, nth_error bs (Z.to_nat (len - 1)) = Some b /\ (bv_unsigned b <= 57)%Z /\
     (forall k, (0 <= k)%Z -> (k * bv_unsigned a1 <= (bv_unsigned a3 - bv_unsigned s5) mod 2 ^ 64)%Z -> (46 <= bv_unsigned b - k)%Z)) ->
  evt rsegs (fun ms' => exists (res : Z) a1' a2' a4' a6' a7' t2' t3' s5' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3 a4' a5 a6' a7' s2 s3 s4 s5' s6 s7 s8 s9 s10 s11 t3' t4 t5 t6) F
               (Z_to_bv 64 0xbcdec) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' shp [CB 1 [Z_to_bv 8 0]] /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z /\ dcls bs' (Z.to_nat len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcbb8) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_037 ())). Qed.

(* [comment removed for export] *)
Lemma rw2_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len shp : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) < 2 ^ 63)%Z ->
  rw_cells rsegs m shp [CB 1 [Z_to_bv 8 0]] -> (shp + 1 <= buf \/ buf + Z.of_nat (length bs) <= shp)%Z -> (0 <= shp)%Z -> (shp + 1 < 2 ^ 63)%Z ->
  (bv_unsigned s0 < Z.of_nat n)%Z -> (1 <= bv_unsigned a4)%Z ->
  a0 = Z_to_bv 64 (buf + (len - 1)) -> t0 = Z_to_bv 64 shp ->
  dcls bs (Z.to_nat (len - 1)) ->
  (exists b, nth_error bs (Z.to_nat (len - 1)) = Some b /\ (46 <= bv_unsigned b <= 57)%Z /\
     (forall k, (1 <= k)%Z -> ((k - 1) * bv_unsigned a4 <= bv_unsigned s0)%Z -> (46 <= bv_unsigned b - k)%Z)) ->
  evt rsegs (fun ms' => exists (res : Z) a1' a2' a4' a5' a7' t3' t5' t6' s0' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 (Z_to_bv 64 res) a1' a2' a3 a4' a5' a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5' t6') F
               (Z_to_bv 64 0xbcdec) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' shp [CB 1 [Z_to_bv 8 0]] /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z /\ dcls bs' (Z.to_nat len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcd10) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_038 ())). Qed.

Ltac setreg2 n e t := let v := getreg n in replace v with e by (symmetry; t).
Open Scope Z_scope.
Lemma land7_0 k : k mod 8 = 0 -> Z.land k 7 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_039 ())). Qed.
Lemma tk_nz dv sh : dv = 100 \/ dv = 10 \/ dv = 1 -> 56 <= sh <= 59 -> 1 <= bv_unsigned (Z_to_bv 64 (Z.shiftl dv (Z.land sh 63))).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_040 ())). Qed.
Lemma tk_nz2 dv sh : dv = 100 \/ dv = 10 \/ dv = 1 -> 56 <= sh <= 59 -> 1 <= bv_unsigned (Z_to_bv 64 (Z.shiftl dv sh)).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_041 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma u8arr_cell m A bs (i : Z) b :
  u8arr rsegs m A bs -> nth_error bs (Z.to_nat i) = Some b -> (0 <= i)%Z -> rw_cells rsegs m (A + i)%Z [CB 1 [b]].
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_042 ())). Qed.
Open Scope Z_scope.
Lemma div8_split b l : b mod 8 = 0 -> (b + l) / 8 = b / 8 + l / 8.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_043 ())). Qed.
Lemma nth3 {T} (b : T) i : (i < 3)%nat -> nth_error [b; b; b] i = Some b.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_044 ())). Qed.
Close Scope Z_scope.

Open Scope Z_scope.
Lemma ksum_val k0 d : - 2 ^ 31 <= k0 < 2 ^ 31 -> Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 k0)) + d) = Z_to_bv 64 (k0 + d).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDgC ()) [] (Mh_0069_blobs1.kr_b_045 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma rw1_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 kap dv sh shl : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) <= 2 ^ 47)%Z -> (Z.of_nat (length bs) < 2 ^ 31)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + Z.of_nat (length bs) <= kp)%Z -> (lenp + 4 <= buf \/ buf + Z.of_nat (length bs) <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z ->
  (buf + Z.of_nat (length bs) <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m shl [CB 1 [Z_to_bv 8 0]] -> (shl = 2147450880 + lenp / 8)%Z ->
  rw_cells rsegs m (2147450880 + buf / 8 + (len - 1) / 8) [CB 1 [Z_to_bv 8 0]] ->
  (bv_unsigned s5 < bv_unsigned a3)%Z -> (56 <= sh <= 59)%Z -> (dv = 100 \/ dv = 10 \/ dv = 1)%Z -> (1 <= kap <= 3)%Z -> (- 2 ^ 20 <= k0 <= 2 ^ 20)%Z ->
  a0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> s1 = Z_to_bv 64 dv -> t4 = Z_to_bv 64 sh -> s0 = Z_to_bv 64 (kap + 1) ->
  t0 = Z_to_bv 64 2147450880 -> t1 = Z_to_bv 64 shl ->
  dcls bs (Z.to_nat (len - 1)) ->
  (exists b, nth_error bs (Z.to_nat (len - 1)) = Some b /\ (bv_unsigned b <= 57)%Z /\
     (forall k, (0 <= k)%Z -> (k * bv_unsigned (Z_to_bv 64 (Z.shiftl dv (Z.land sh 63))) <= (bv_unsigned a3 - bv_unsigned s5) mod 2 ^ 64)%Z -> (46 <= bv_unsigned b - k)%Z)) ->
  evt rsegs (fun ms' => exists (res : Z) t0' t3' t5' a1' a2' a4' a5' a6' a7' t2' s5' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1 t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3 a4' a5' a6' a7' s2 s3 s4 s5' s6 s7 s8 s9 s10 s11 t3' t4 t5' t6) F
               (Z_to_bv 64 0xbcdec) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs)); (kp, kp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + (kap - 1)))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)]
      /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z /\ dcls bs' (Z.to_nat len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcb64) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_046 ())). Qed.

(* [comment removed for export] *)
Lemma rw2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 kap shl : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> (1 <= len <= Z.of_nat (length bs))%Z -> (buf + Z.of_nat (length bs) <= 2 ^ 47)%Z -> (Z.of_nat (length bs) < 2 ^ 31)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + Z.of_nat (length bs) <= kp)%Z -> (lenp + 4 <= buf \/ buf + Z.of_nat (length bs) <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z ->
  (buf + Z.of_nat (length bs) <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m shl [CB 1 [Z_to_bv 8 0]] -> (shl = 2147450880 + lenp / 8)%Z ->
  rw_cells rsegs m (2147450880 + buf / 8 + (len - 1) / 8) [CB 1 [Z_to_bv 8 0]] ->
  (1 <= bv_unsigned a4)%Z -> (- 2 ^ 20 <= kap <= 0)%Z -> (- 2 ^ 20 <= k0 <= 2 ^ 20)%Z ->
  a0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> s1 = Z_to_bv 64 kap -> t0 = Z_to_bv 64 2147450880 -> t1 = Z_to_bv 64 shl ->
  (bv_unsigned t3 < bv_unsigned a3)%Z -> (bv_unsigned s0 * 10 = bv_unsigned a3)%Z -> (bv_unsigned a4 + bv_unsigned a3 < 2 ^ 64)%Z ->
  dcls bs (Z.to_nat (len - 1)) ->
  (exists b, nth_error bs (Z.to_nat (len - 1)) = Some b /\ (bv_unsigned b <= 57)%Z /\
     (forall k, (0 <= k)%Z -> (k * bv_unsigned a4 <= bv_unsigned a3 - bv_unsigned t3)%Z -> (46 <= bv_unsigned b - k)%Z)) ->
  evt rsegs (fun ms' => exists (res : Z) t0' t1' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6' s0' s1' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 s0' s1' (Z_to_bv 64 res) a1' a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (Z_to_bv 64 0xbcdec) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + Z.of_nat (length bs)); (kp, kp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + kap))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)]
      /\ length bs' = length bs /\ (res = 0 \/ res = 1)%Z /\ dcls bs' (Z.to_nat len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcc9c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_047 ())). Qed.

(* [comment removed for export] *)
Lemma loop2_walk : forall (k n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 sh Dl p2 shl : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m shl [CB 1 [Z_to_bv 8 0]] -> (shl = 2147450880 + lenp / 8)%Z ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  (n + k = 18)%nat -> (10 ^ Z.of_nat n <= Dl)%Z -> (Dl <= p2 < 2 ^ sh)%Z -> (56 <= sh <= 59)%Z -> (1 <= len <= 3 + Z.of_nat n)%Z -> (- 2 ^ 19 <= k0 <= 2 ^ 19)%Z ->
  a0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> s1 = Z_to_bv 64 (- Z.of_nat n) -> t4 = Z_to_bv 64 sh -> s2 = Z_to_bv 64 10 ->
  a3 = Z_to_bv 64 Dl -> t3 = Z_to_bv 64 p2 -> t6 = Z_to_bv 64 (2 ^ sh - 1) -> a4 = Z_to_bv 64 (2 ^ sh) -> t5 = Z_to_bv 64 4294967295 ->
  t0 = Z_to_bv 64 2147450880 -> t1 = Z_to_bv 64 shl ->
  dcls bs (Z.to_nat len) ->
  evt rsegs (fun ms' => exists (res len' dk : Z) t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s3' s4' t3' t4' t5' t6' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (Z_to_bv 64 0xbcdec) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + dk))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-18 <= dk <= 2)%Z /\ dcls bs' (Z.to_nat len'))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcc0c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_048 ())). Qed.

End VaWkDgC.
Module VaWkDg2C.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDgC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VaWkDg2C () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib6VdMath3VDM4hideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg4nth3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00697VaWkDgC4nth3C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions8bv_swrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_posC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00597WdWkKit=swrap32_smallC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_divuwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_bound".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Asan.M.loaded_segments (only parsing).

Open Scope Z_scope.
Definition dvk (j : nat) : Z := match j with 3%nat => 100 | 2%nat => 10 | _ => 1 end.
Lemma divuw_val (x d : Z) : 0 <= x < 2 ^ 31 -> 0 < d < 2 ^ 31 -> v_divuw (Z_to_bv 64 x) (Z_to_bv 64 d) = Z_to_bv 64 (x / d).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg2C ()) [] (Mh_0069_blobs1.kr_b_049 ())). Qed.
Lemma divuw_valw (wx : word) (d : Z) : bv_unsigned wx < 2 ^ 31 -> 0 < d < 2 ^ 31 -> v_divuw wx (Z_to_bv 64 d) = Z_to_bv 64 (bv_unsigned wx / d).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkDg2C ()) [] (Mh_0069_blobs1.kr_b_050 ())). Qed.
Close Scope Z_scope.
(* [comment removed for export] *)
Ltac hid H := let T := type of H in change (VDM.hide T) in H.

(* [comment removed for export] *)
Lemma kloop_walk : forall (j : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (buf len kp lenp k0 sh Dl p1 Wp1 shl : Z) (bs : list byte),
  mem_inv rsegs m -> u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m shl [CB 1 [Z_to_bv 8 0]] -> (shl = 2147450880 + lenp / 8)%Z ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  (1 <= j <= 3)%nat -> (56 <= sh <= 59)%Z -> (1 <= Dl <= Wp1)%Z -> (2 ^ sh <= Wp1 < 2 ^ 64)%Z -> (0 <= p1 < 10 * dvk j)%Z -> (0 <= len <= 3 - Z.of_nat j)%Z ->
  (len = 0 -> p1 = Wp1 / 2 ^ sh)%Z -> (- 2 ^ 19 <= k0 <= 2 ^ 19)%Z ->
  a0 = Z_to_bv 64 kp -> a7 = Z_to_bv 64 lenp -> a6 = Z_to_bv 64 buf -> s2 = Z_to_bv 64 1 -> t4 = Z_to_bv 64 sh ->
  a3 = Z_to_bv 64 Dl -> t3 = Z_to_bv 64 (Wp1 mod 2 ^ sh) -> t6 = Z_to_bv 64 (2 ^ sh - 1) -> a4 = Z_to_bv 64 (2 ^ sh) ->
  s3 = Z_to_bv 64 p1 -> s1 = Z_to_bv 64 (dvk j) -> s0 = Z_to_bv 64 (Z.of_nat j + 1) -> s4 = Z_to_bv 64 0xcccccccd00000000 -> t5 = Z_to_bv 64 4294967295 ->
  t0 = Z_to_bv 64 2147450880 -> t1 = Z_to_bv 64 shl ->
  (Dl <= p1 * 2 ^ sh + Wp1 mod 2 ^ sh <= Wp1)%Z ->
  dcls bs (Z.to_nat len) ->
  evt rsegs (fun ms' => exists (res len' dk : Z) t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (Z_to_bv 64 0xbcdec) fc None m' (seg_rom rsegs)
      /\ munch [(buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + dk))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-18 <= dk <= 2)%Z /\ dcls bs' (Z.to_nat len'))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbcacc) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_051 ())). Qed.

End VaWkDg2C.
Module VaWkDg3C.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDgC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg2C.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Asan.M.loaded_segments (only parsing).

Definition dg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo buf kp lenp k0 : Z) : machine_state -> Prop :=
  fun ms' => exists (res len' dk : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (bs' : list byte) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
               (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (buf, buf + 22); (kp, kp + 4); (lenp, lenp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (bv_unsigned sp) [C8 (Z_to_bv 64 kp)] /\ u8arr rsegs m' buf bs'
      /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (k0 + dk))] /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len')]
      /\ length bs' = 22%nat /\ (res = 0 \/ res = 1)%Z /\ (1 <= len' <= 21)%Z /\ (-18 <= dk <= 2)%Z /\ dcls bs' (Z.to_nat len').

(* [comment removed for export] *)
Lemma dg_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp k0 Wm W Wp E e1 e3 e5 : Z) (bs lb : list byte),
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> (lo + 80 <= bv_unsigned sp)%Z -> (bv_unsigned sp + 8 <= 2 ^ 47)%Z -> (0x6b6000 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 kp)] ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 k0)] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp + 8 <= kp \/ kp + 4 <= lo)%Z -> (bv_unsigned sp + 8 <= lenp \/ lenp + 4 <= lo)%Z -> (bv_unsigned sp + 8 <= buf \/ buf + 22 <= lo)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z ->
  (bv_unsigned sp + 8 <= 2147446784 \/ 17594333495296 <= lo)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  ro_cells rsegs m 0x156d98 [C8 (Z_to_bv 64 0x15fa78)] -> ro_cells rsegs m 0x15fa78 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m (2147450880 + lenp / 8) [CB 1 [Z_to_bv 8 0]] ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  (1 <= Wm <= Wp)%Z -> (W <= Wp)%Z -> (0 <= W)%Z -> (2 ^ 59 <= Wp <= 2 ^ 64 - 2)%Z -> (-59 <= E <= -56)%Z -> (- 2 ^ 19 <= k0 <= 2 ^ 19)%Z ->
  (0 <= e1 < 2 ^ 64)%Z -> (0 <= e3 < 2 ^ 64)%Z -> (0 <= e5 < 2 ^ 64)%Z -> bv_swrap 32 e1 = E -> bv_swrap 32 e3 = E -> bv_swrap 32 e5 = E ->
  a0 = Z_to_bv 64 Wm -> a1 = Z_to_bv 64 e1 -> a2 = Z_to_bv 64 W -> a3 = Z_to_bv 64 e3 -> a4 = Z_to_bv 64 Wp -> a5 = Z_to_bv 64 e5 ->
  a6 = Z_to_bv 64 buf -> a7 = Z_to_bv 64 lenp ->
  evt rsegs (dg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo buf kp lenp k0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbca0c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_052 ())). Qed.

End VaWkDg3C.
Module VaWkGC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath VaTab. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VaTab OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDgC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg2C OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg3C.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VaWkGC () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib6VdMath3VDM4hideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg4nth3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00697VaWkDgC4nth3C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC56Stdlib6ZArith6BinInt1Z4onesK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z9land_onesC59OSSVerify5KrLib6VdMath3VDM8land_W64C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Asan.M.loaded_segments (only parsing).

Open Scope Z_scope.
Lemma land_W_M32 x : Z.land (Z.land x 18446744073709551615) 4294967295 = x mod 2 ^ 32.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkGC ()) [] (Mh_0069_blobs1.kr_b_053 ())). Qed.
Close Scope Z_scope.

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
Lemma c2_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (spz lo buf kp lenp mk Wm W Wp E e1 : Z) (junk8 bs kb lb : list byte) (o_ra o_s0 o_s1 o_s2 o_s3 o_s4 o_s5 o_s6 o_s7 : word),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo spz -> (lo + 80 <= spz)%Z -> (spz + 80 <= 2 ^ 47)%Z -> (0x6b6000 <= lo)%Z -> (bv_unsigned o_ra mod 2 = 0)%Z ->
  rw_cells rsegs m spz [CB 8 junk8; C8 o_s7; C8 o_s6; C8 o_s5; C8 o_s4; C8 o_s3; C8 o_s2; C8 o_s1; C8 o_s0; C8 o_ra] ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (spz + 80 <= kp \/ kp + 4 <= lo)%Z -> (spz + 80 <= lenp \/ lenp + 4 <= lo)%Z -> (spz + 80 <= buf \/ buf + 22 <= lo)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z -> (0x6b6000 <= kp)%Z ->
  (spz + 80 <= 2147446784 \/ 17594333495296 <= lo)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  ro_cells rsegs m 0x156d98 [C8 (Z_to_bv 64 0x15fa78)] -> ro_cells rsegs m 0x15fa78 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m (2147450880 + lenp / 8) [CB 1 [Z_to_bv 8 0]] ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  (-307 <= mk <= 325)%Z -> (1 <= Wm <= W)%Z -> (W <= Wp)%Z -> (2 ^ 62 <= Wp <= 2 ^ 64 - 2)%Z -> (-59 <= E <= -56)%Z -> (0 <= e1 < 2 ^ 32)%Z -> bv_swrap 32 e1 = E ->
  a0 = Z_to_bv 64 Wm -> a1 = Z_to_bv 64 e1 -> a2 = Z_to_bv 64 kp -> a3 = Z_to_bv 64 e1 -> a4 = Z_to_bv 64 Wp -> a5 = Z_to_bv 64 W -> t2 = Z_to_bv 64 (- mk) ->
  s0 = Z_to_bv 64 lenp -> s1 = Z_to_bv 64 buf -> s2 = Z_to_bv 64 2147450880 -> sp = Z_to_bv 64 spz ->
  evt rsegs (g_post o_ra (Z_to_bv 64 (spz + 80)) gp tp o_s0 o_s1 o_s2 o_s3 o_s4 o_s5 o_s6 o_s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbc0e0) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_054 ())). Qed.

(* [comment removed for export] *)
Lemma grisu_c2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (spz lo buf kp lenp mi mie pe P Wn sh : Z) (junk8 bs kb lb zf ze : list byte) (o_ra o_s0 o_s1 o_s2 o_s3 o_s4 o_s5 o_s6 o_s7 : word),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo spz -> (lo + 80 <= spz)%Z -> (spz + 80 <= 2 ^ 47)%Z -> (0x6b6000 <= lo)%Z -> (bv_unsigned o_ra mod 2 = 0)%Z ->
  rw_cells rsegs m spz [CB 8 junk8; C8 o_s7; C8 o_s6; C8 o_s5; C8 o_s4; C8 o_s3; C8 o_s2; C8 o_s1; C8 o_s0; C8 o_ra] ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (spz + 80 <= kp \/ kp + 4 <= lo)%Z -> (spz + 80 <= lenp \/ lenp + 4 <= lo)%Z -> (spz + 80 <= buf \/ buf + 22 <= lo)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z -> (0x6b6000 <= kp)%Z ->
  (spz + 80 <= 2147446784 \/ 17594333495296 <= lo)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  ro_cells rsegs m 0x156d98 [C8 (Z_to_bv 64 0x15fa78)] -> ro_cells rsegs m 0x15fa78 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m (2147450880 + lenp / 8) [CB 1 [Z_to_bv 8 0]] ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  u8arr rsegs m (2147450880 + 18316) zf -> length zf = 687%nat -> (forall i, (i < 687)%nat -> nth_error zf i = Some (Z_to_bv 8 0)) ->
  u8arr rsegs m (2147450880 + 19172) ze -> length ze = 343%nat -> (forall i, (i < 343)%nat -> nth_error ze i = Some (Z_to_bv 8 0)) ->
  (1 <= mi)%Z -> (sh = mie - pe + 10)%Z -> (9 <= sh <= 62)%Z -> (mi * 2 ^ sh <= Wn * 2 ^ 11)%Z -> (Wn * 2 ^ 11 <= P * 2 ^ 10)%Z -> (2 ^ 63 <= P * 2 ^ 10 < 2 ^ 64)%Z ->
  (-1021 <= -50 - pe <= 1077)%Z -> (-2000 <= mie <= 2000)%Z -> (0 <= Wn)%Z -> (0 <= P)%Z ->
  a4 = Z_to_bv 64 (pe + 1) -> a2 = Z_to_bv 64 kp -> a3 = Z_to_bv 64 mie -> t1 = Z_to_bv 64 pe -> a6 = Z_to_bv 64 Wn -> a7 = Z_to_bv 64 mi ->
  t0 = Z_to_bv 64 P -> s0 = Z_to_bv 64 lenp -> s1 = Z_to_bv 64 buf -> s2 = Z_to_bv 64 2147450880 -> sp = Z_to_bv 64 spz ->
  evt rsegs (g_post o_ra (Z_to_bv 64 (spz + 80)) gp tp o_s0 o_s1 o_s2 o_s3 o_s4 o_s5 o_s6 o_s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbbf20) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_055 ())). Qed.

End VaWkGC.
Module VaWkGpC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WdGrows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WdGrows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require VdMath VaTab. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VdMath OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.VaTab OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDgC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg2C OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkDg3C OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.VaWkGC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_VaWkGpC () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib6VdMath3VDM4hideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg4nth3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00697VaWkDgC4nth3C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z:pow_succ_rK4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec7alu_andC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09I4ELinuxProcessSemantics5Riscv7Prelude4tree00C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC49OSSVerify5KrLib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr08K47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib6VdMath3VDM<land_pow2_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2ex01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01C59OSSVerify5KrLib6VdMath3VDM<land_pow2_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz01I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega6VarMap1t03C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge=bv_lts_zero_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtK4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C56Stdlib6ZArith6BinInt1Z9log2_specC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rK46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05C56Stdlib6ZArith4Znat5Z2Nat2idC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib5Lists4List9nth_errorC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00392FP4frm0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics5Riscv3Sem7reg_getC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00C47Corelib4Init9Datatypes6lengthK79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8ro_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC47Corelib4Init5Peano2ltc59OSSVerify5KrLib7Mh_00696VaWkGC6g_postC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc59OSSVerify5KrLib7Mh_00697VaWkGpC<grisu_d_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00697VaWkGpC<grisu_n_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr5u8arrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Asan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
Lemma lpA_walk : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (X e : Z),
  (1 <= n)%nat -> (2 ^ 53 <= X * 2 ^ Z.of_nat n < 2 ^ 54)%Z -> (0 <= X)%Z ->
  a5 = Z_to_bv 64 4503599627370496 -> t0 = Z_to_bv 64 X -> t1 = Z_to_bv 64 e ->
  evt rsegs (fun ms' => exists a4',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (X * 2 ^ Z.of_nat n)) (Z_to_bv 64 (e - Z.of_nat n)) t2 s0 s1 a0 a1 a2 a3 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0xbbedc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbbecc) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkGpC ()) [] (Mh_0069_blobs1.kr_b_056 ())). Qed.

(* [comment removed for export] *)
Lemma lpB_walk : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (Y e : Z),
  (1 <= n)%nat -> (2 ^ 52 <= Y * 2 ^ Z.of_nat n < 2 ^ 53)%Z -> (0 <= Y)%Z ->
  a6 = Z_to_bv 64 Y -> a4 = Z_to_bv 64 e ->
  evt rsegs (fun ms' => exists a5',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (e - Z.of_nat n)) a5' (Z_to_bv 64 (Y * 2 ^ Z.of_nat n)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0xbbef0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbbee0) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkGpC ()) [] (Mh_0069_blobs1.kr_b_057 ())). Qed.

(* [comment removed for export] *)
Lemma grisu_n_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp u : Z) (bs kb lb zf ze : list byte),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo (bv_unsigned sp) -> (lo + 160 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= 2 ^ 47)%Z -> (0x6b6000 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (forall r, bv_unsigned r = 10%Z -> reg_get F r = Z_to_bv 64 u) -> (2 ^ 52 <= u < 2 ^ 63)%Z ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp <= kp \/ kp + 4 <= lo)%Z -> (bv_unsigned sp <= lenp \/ lenp + 4 <= lo)%Z -> (bv_unsigned sp <= buf \/ buf + 22 <= lo)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z -> (0x6b6000 <= kp)%Z ->
  (bv_unsigned sp <= 2147446784 \/ 17594333495296 <= lo)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  ro_cells rsegs m 0x156d98 [C8 (Z_to_bv 64 0x15fa78)] -> ro_cells rsegs m 0x15fa78 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m (2147450880 + lenp / 8) [CB 1 [Z_to_bv 8 0]] ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  u8arr rsegs m (2147450880 + 18316) zf -> length zf = 687%nat -> (forall i, (i < 687)%nat -> nth_error zf i = Some (Z_to_bv 8 0)) ->
  u8arr rsegs m (2147450880 + 19172) ze -> length ze = 343%nat -> (forall i, (i < 343)%nat -> nth_error ze i = Some (Z_to_bv 8 0)) ->
  a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 lenp -> a2 = Z_to_bv 64 kp ->
  evt rsegs (g_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbbe40) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_058 ())). Qed.

Open Scope Z_scope.
Lemma dn_facts f : 1 <= f < 2 ^ 52 -> exists n : nat, (1 <= n <= 52)%nat /\ 2 ^ 52 <= f * 2 ^ Z.of_nat n < 2 ^ 53 /\ 2 ^ 53 <= (2 * f + 1) * 2 ^ Z.of_nat n < 2 ^ 54.
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkGpC ()) [] (Mh_0069_blobs1.kr_b_059 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma grisu_d_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp u : Z) (bs kb lb zf ze : list byte),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo (bv_unsigned sp) -> (lo + 160 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= 2 ^ 47)%Z -> (0x6b6000 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (forall r, bv_unsigned r = 10%Z -> reg_get F r = Z_to_bv 64 u) -> (1 <= u < 2 ^ 52)%Z ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp <= kp \/ kp + 4 <= lo)%Z -> (bv_unsigned sp <= lenp \/ lenp + 4 <= lo)%Z -> (bv_unsigned sp <= buf \/ buf + 22 <= lo)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z -> (0x6b6000 <= kp)%Z ->
  (bv_unsigned sp <= 2147446784 \/ 17594333495296 <= lo)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  ro_cells rsegs m 0x156d98 [C8 (Z_to_bv 64 0x15fa78)] -> ro_cells rsegs m 0x15fa78 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m (2147450880 + lenp / 8) [CB 1 [Z_to_bv 8 0]] ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  u8arr rsegs m (2147450880 + 18316) zf -> length zf = 687%nat -> (forall i, (i < 687)%nat -> nth_error zf i = Some (Z_to_bv 8 0)) ->
  u8arr rsegs m (2147450880 + 19172) ze -> length ze = 343%nat -> (forall i, (i < 343)%nat -> nth_error ze i = Some (Z_to_bv 8 0)) ->
  a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 lenp -> a2 = Z_to_bv 64 kp ->
  evt rsegs (g_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbbe40) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_060 ())). Qed.

(* [comment removed for export] *)
Theorem grisu3_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (lo buf kp lenp u : Z) (bs kb lb zf ze : list byte),
  mem_inv rsegs m -> frm0 fc -> stk rsegs m lo (bv_unsigned sp) -> (lo + 160 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= 2 ^ 47)%Z -> (0x6b6000 <= lo)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
  (forall r, bv_unsigned r = 10%Z -> reg_get F r = Z_to_bv 64 u) -> (1 <= u < 2 ^ 63)%Z ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> (buf + 22 <= 2 ^ 47)%Z ->
  rw_cells rsegs m kp [CB 4 kb] -> rw_cells rsegs m lenp [CB 4 lb] ->
  (kp + 4 <= buf \/ buf + 22 <= kp)%Z -> (lenp + 4 <= buf \/ buf + 22 <= lenp)%Z -> (kp + 4 <= lenp \/ lenp + 4 <= kp)%Z ->
  (bv_unsigned sp <= kp \/ kp + 4 <= lo)%Z -> (bv_unsigned sp <= lenp \/ lenp + 4 <= lo)%Z -> (bv_unsigned sp <= buf \/ buf + 22 <= lo)%Z ->
  (kp + 4 <= 2 ^ 47)%Z -> (lenp + 4 <= 2 ^ 47)%Z -> (buf mod 8 = 0)%Z -> (0x6b6000 <= kp)%Z ->
  (bv_unsigned sp <= 2147446784 \/ 17594333495296 <= lo)%Z ->
  (buf + 22 <= 2147446784 \/ 17594333495296 <= buf)%Z -> (kp + 4 <= 2147446784 \/ 17594333495296 <= kp)%Z ->
  (lenp + 4 <= 2147446784 \/ 17594333495296 <= lenp)%Z ->
  ro_cells rsegs m 0x156d98 [C8 (Z_to_bv 64 0x15fa78)] -> ro_cells rsegs m 0x15fa78 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells rsegs m (2147450880 + kp / 8) [CB 1 [Z_to_bv 8 0]] -> rw_cells rsegs m (2147450880 + lenp / 8) [CB 1 [Z_to_bv 8 0]] ->
  u8arr rsegs m (2147450880 + buf / 8) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  u8arr rsegs m (2147450880 + 18316) zf -> length zf = 687%nat -> (forall i, (i < 687)%nat -> nth_error zf i = Some (Z_to_bv 8 0)) ->
  u8arr rsegs m (2147450880 + 19172) ze -> length ze = 343%nat -> (forall i, (i < 343)%nat -> nth_error ze i = Some (Z_to_bv 8 0)) ->
  a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 lenp -> a2 = Z_to_bv 64 kp ->
  evt rsegs (g_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo buf kp lenp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0xbbe40) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_VaWkGpC ()) [] (Mh_0069_blobs1.kr_b_061 ())). Qed.

End VaWkGpC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WaShape. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.muslA.Mh_0068.
Module WaWkOut.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require WaShape. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.WaShape.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.muslA.Mh_0068.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WaWkOut () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib6VdMath3VDM4hideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg4nth3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00697VaWkDgC4nth3C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem5wr_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells;cells_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_wfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8bytes_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan]Tgt_fuzz_msgpack_encoder_asan_loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes3nat00C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr5u8arrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3addC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem9upd_bytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393MemEbytes_at_write_insideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem;wr_at_writeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem@upd_bytes_lengthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Asan_loaded_segments (only parsing).

(* [comment removed for export] *)
Lemma cells_reshape m A cs cs' :
  rw_cells rsegs m A cs -> cells_bytes cs' = cells_bytes cs -> cells_wf cs' -> rw_cells rsegs m A cs'.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkOut ()) [] (Mh_0069_blobs1.kr_b_062 ())). Qed.

(* [comment removed for export] *)
Record fjunk := FJ { fj0 : list byte; fj1 : list byte; fj2 : list byte; fj3 : list byte; fj4 : list byte; fj5 : list byte;
                     fj6 : list byte; fj7 : list byte }.
(* [comment removed for export] *)
Definition zflags : list byte := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition fileC (flags : list byte) (rpos rend wend wpos wbase wfn bufp bsz mode lockv lbf cookie : word) (J : fjunk) : list cell :=
  [CB 4 flags; CB 4 (fj0 J); C8 rpos; C8 rend; CB 8 (fj1 J); C8 wend; C8 wpos; CB 8 (fj2 J); C8 wbase; CB 8 (fj3 J); C8 wfn;
   CB 8 (fj4 J); C8 bufp; C8 bsz; CB 32 (fj5 J); C4 mode; C4 lockv; C4 lbf; CB 4 (fj6 J); C8 cookie; CB 72 (fj7 J)].

(* [comment removed for export] *)
Lemma towrite_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (fa bufp bsz mode : Z) (rpos rend wend wpos wbase wfn lockv lbf cookie : word) (J : fjunk),
  mem_inv rsegs m -> a0 = Z_to_bv 64 fa -> (-2 ^ 31 <= mode < 2 ^ 31)%Z ->
  (0 <= bufp)%Z -> (0 <= bsz)%Z -> (bufp + bsz < 2 ^ 63)%Z -> (fa + 232 < 2 ^ 64)%Z ->
  rw_cells rsegs m fa (fileC zflags rpos rend wend wpos wbase wfn (Z_to_bv 64 bufp) (Z_to_bv 64 bsz) (Z_to_bv 64 mode) lockv lbf cookie J) ->
  evt rsegs (fun ms' => exists a1' a2' a3' (mode' : Z) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(fa, fa + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' fa (fileC zflags (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bufp + bsz)) (Z_to_bv 64 bufp) (Z_to_bv 64 bufp) wfn
                                  (Z_to_bv 64 bufp) (Z_to_bv 64 bsz) (Z_to_bv 64 mode') lockv lbf cookie J))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x13ffc8) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_063 ())). Qed.

Lemma u8arr_write_bytes m A bs (k : Z) xs :
  u8arr rsegs m A bs -> (0 <= k)%Z -> (Z.to_nat k + length xs <= length bs)%nat ->
  u8arr rsegs (write_to_mem m (wa (A + k)) xs) A (upd_bytes bs (Z.to_nat k) xs).
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkOut ()) [] (Mh_0069_blobs1.kr_b_064 ())). Qed.

(* [comment removed for export] *)

End WaWkOut.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0064.
Module WaWkFmtE.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0064. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0059.WdWkMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0064.WaWkFmtB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0064.WaWkFmtC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0064.WaWkFmtD OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0069.WaWkOut.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WaWkFmtE () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib6VdMath3VDM4hideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00696VaWkDg4nth3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00697VaWkDgC4nth3C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393ArrCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr6u32arrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib7Mh_00648WaWkFmtB8limbs_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr<u32arr_boundC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbC49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic5proj2C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge8bv_ltu_ZC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00648WaWkFmtB<limbs_ok_nthC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem2waC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr;u32arr_readC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00597WdWkKit@unsigned_small64C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem4sx32C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics5Riscv3Sem4core01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K47Corelib7Numbers7BinNums1Z03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_indC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge8bv_eqb_ZC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqK47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_00648WaWkFmtB;sx32_smallwC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify5KrLib2CJ3Lib7Mh_00397StepKit<evt_step_genC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C49OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan]Tgt_fuzz_msgpack_encoder_asan_loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5msize03I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState6w0_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00597WdWkKit=swrap32_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC49OSSVerify5KrLib8PropExec7v_remuwC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BC49OSSVerify5KrLib8PropExec5v_mulC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC49OSSVerify5KrLib8PropExec5m_mulC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0CC4ELinuxProcessSemantics5Riscv3Sem5low32C49OSSVerify5KrLib8PropExec7w_remuwC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c59OSSVerify5KrLib7Mh_00698WaWkFmtE9remuw_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z4succK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith6BinInt1Z8mul_commC79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_litC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5mulop08K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z4lxorC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geC59OSSVerify5KrLib7Mh_00597WdWkKit=lxor_sign_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lxor_0_rC56Stdlib6ZArith6BinInt1Z:lxor_assocC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z4landC69OSSVerify5KrLib2CJ3Lib7SFModel8land_W64C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith8Zbitwise1Z?sub_land_same_lC56Stdlib6ZArith6BinInt1Z:ldiff_landC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z@ldiff_ones_l_lowC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z<lor_ones_lowC56Stdlib6ZArith6BinInt1Z8lor_commC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z7add_modC56Stdlib6ZArith6BinInt1Z?mul_mod_idemp_lC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z7mod_modC56Stdlib6ZArith6BinInt1Z5max_rC56Stdlib6ZArith6BinInt1Z5max_lC56Stdlib6ZArith6BinInt1Z8land_0_lC56Stdlib6ZArith6BinInt1Z>div_unique_posC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7div_divc59OSSVerify5KrLib7Mh_00698WaWkFmtE>swrap32_addk32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3absC56Stdlib6ZArith6BinInt1Z8abs_specc59OSSVerify5KrLib7Mh_00698WaWkFmtE4notWC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7sub_0_rC56Stdlib6ZArith6BinInt1Z9div_smallc59OSSVerify5KrLib7Mh_00698WaWkFmtE;swrap32_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE=div10_magic64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundc59OSSVerify5KrLib7Mh_00698WaWkFmtE5lor48C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:div_uniqueK79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:munch_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame:wmono_reflC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=C49OSSVerify5KrLib8PropExec6v_addwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu32C49OSSVerify5KrLib8PropExec6w_addwC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells6cbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem3le8C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8load_u64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells5csizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC79OSSVerify5KrLib2CJ3Lib7Mh_00394Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C49OSSVerify5KrLib8PropExec5v_xorC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_xorC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC69OSSVerify5KrLib2CJ3Lib7SFModel;signed_of_ZC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem:length_le8C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6insideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_writeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_writeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC49OSSVerify5KrLib8PropExec5b_luiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_andC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem7mem_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame5wmonoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells7cell_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC79OSSVerify5KrLib2CJ3Lib7Mh_00394StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphI79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C49OSSVerify5KrLib8PropExec6v_subwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6w_subwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_sltC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_sltC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_subC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03c59OSSVerify5KrLib7Mh_00698WaWkFmtE9ztb_landWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE:max0_idiomC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE7sgn_keyC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridgeAunsigned_lit_landC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge6zr_b2zC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00397ZBridge9v_slt_b2zC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop04c59OSSVerify5KrLib7Mh_00698WaWkFmtE4fstyC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib7Mh_00597WdWkMem>rw_cells_take3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE;fmtE1a_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE<fmtE1b0_walkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8le_min_lC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z;min_glb_iffC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z8min_specc59OSSVerify5KrLib7Mh_00698WaWkFmtE;fmtE1f_walkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE;fmtE1t_walkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec7evt_cutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00698WaWkFmtE4stE1C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3subc59OSSVerify5KrLib7Mh_00698WaWkFmtE9estr_walkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Arr@u32arr_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula09C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame7outsideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame6sub_fpC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame<munch_weakenC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;munch_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame;wmono_transC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addI47Corelib5Lists7ListDef6Forall00c59OSSVerify5KrLib7Mh_00698WaWkFmtE6isdigbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_add".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := Asan_loaded_segments (only parsing).

(* [comment removed for export] *)
Lemma stripE_walk : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (B ia iz ir : Z) (ws : list word),
  u32arr rsegs m B ws -> (0 <= ia <= iz)%Z -> (iz <= Z.of_nat (length ws))%Z -> (iz - ia <= Z.of_nat n)%Z -> (B + 4 * Z.of_nat (length ws) < 2 ^ 63)%Z ->
  (0 <= ir <= 128)%Z -> limbs_ok ws ia iz ->
  evt rsegs (fun ms' => exists (iz' : Z) a1' a2' s11',
      (ia <= iz' <= iz)%Z /\ (forall k w, (iz' <= k < iz)%Z -> nth_error ws (Z.to_nat k) = Some w -> bv_unsigned w = 0%Z) /\
      (iz' = ia \/ exists w, nth_error ws (Z.to_nat (iz' - 1)) = Some w /\ bv_unsigned w <> 0%Z) /\
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (B + 4 * ia)) (Z_to_bv 64 (4 * (iz' - ir))) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                    (Z_to_bv 64 (B + 4 * iz')) s8 s9 s10 s11' t3 t4 t5 t6) F
               (Z_to_bv 64 0x142628) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (B + 4 * ia)) a0 (Z_to_bv 64 (4 * (iz - ir))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             (Z_to_bv 64 (B + 4 * iz)) t3 t4 t5 t6) F (Z_to_bv 64 0x14260c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs1.kr_b_065 ())). Qed.

Open Scope Z_scope.
Lemma remuw_val (wx : word) (d : Z) : bv_unsigned wx < 2 ^ 31 -> 0 < d < 2 ^ 31 -> v_remuw wx (Z_to_bv 64 d) = Z_to_bv 64 (bv_unsigned wx mod d).
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs1.kr_b_066 ())). Qed.
Close Scope Z_scope.

Ltac case_cond := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let H := fresh "HC" in destruct c eqn:H end.

(* [comment removed for export] *)
Lemma tzloop_walk : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) fc m (wx : word) (j : Z),
  (0 < bv_unsigned wx < 1000000000)%Z -> (0 <= j <= 7)%Z -> (7 - j <= Z.of_nat n)%Z ->
  evt rsegs (fun ms' => exists (j' : Z) a4' a5',
      (j + 1 <= j' <= 8)%Z /\
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 j') wx (Z_to_bv 64 10) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
               (Z_to_bv 64 0x1426d8) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 j) wx (Z_to_bv 64 10) (Z_to_bv 64 (10 ^ (j + 1))) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 0x1426c8) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs1.kr_b_067 ())). Qed.

Open Scope Z_scope.
Lemma sgn_key x : -2 ^ 63 <= x < 2 ^ 63 -> Z.lxor (Z.land x 18446744073709551615) 9223372036854775808 = x + 9223372036854775808.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs1.kr_b_068 ())). Qed.
Lemma notW v : 0 <= v < 2 ^ 64 -> Z.lxor v 18446744073709551615 = 18446744073709551615 - v.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs1.kr_b_069 ())). Qed.
Lemma lorW_l v : 0 <= v < 2 ^ 64 -> Z.lor 18446744073709551615 v = 18446744073709551615.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs1.kr_b_070 ())). Qed.
Definition fsty (e p : Z) : bool := (-4 <=? e) && (e <? p).
Close Scope Z_scope.

Open Scope Z_scope.
Lemma swrap32_addk32 x k : bv_swrap 32 (x + 4294967296 * k) = bv_swrap 32 x.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs1.kr_b_071 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma fmtE1a_walk : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 s8 s9 s10 t3 t5 t6 : word)
   (F : bvmap 5 word) fc m (B ia iz ir e p : Z) (ws : list word) (cw ct : word) (jB : list byte),
  mem_inv rsegs m -> u32arr rsegs m B ws -> (0 <= ia < iz)%Z -> (iz <= Z.of_nat (length ws))%Z -> (Z.of_nat (length ws) <= 128)%Z ->
  (0 <= ir <= 122)%Z -> (B + 4 * Z.of_nat (length ws) < 2 ^ 63)%Z -> limbs_ok ws ia iz -> (-1200 < e < 1200)%Z -> (9 <= p <= 20)%Z ->
  rw_cells rsegs m (bv_unsigned s0 + -496) [C8 cw; C8 ct; CB 8 jB; C8 (Z_to_bv 64 0)] ->
  (B + 4 * Z.of_nat (length ws) <= bv_unsigned s0 - 544)%Z -> (bv_unsigned s0 < 2 ^ 63)%Z ->
  evt rsegs (fun ms' => exists (iz' : Z) a2' a3' a4' s11',
      (ia <= iz' <= iz)%Z /\ (forall k w, (iz' <= k < iz)%Z -> nth_error ws (Z.to_nat k) = Some w -> bv_unsigned w = 0%Z) /\
      (iz' = ia \/ exists w, nth_error ws (Z.to_nat (iz' - 1)) = Some w /\ bv_unsigned w <> 0%Z) /\
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (B + 4 * ia)) (Z_to_bv 64 (4 * (iz' - ir))) (Z_to_bv 64 p) a2' a3' a4' a5 a6 a7
                    (Z_to_bv 64 (if fsty e p then p - 1 - e else p - 1)) s3 (Z_to_bv 64 103) (Z_to_bv 64 e) (Z_to_bv 64 (B + 4 * ir))
                    (Z_to_bv 64 (B + 4 * iz')) s8 s9 s10 s11' (Z_to_bv 64 0) (Z_to_bv 64 (if fsty e p then 102 else 101)) (Z_to_bv 64 0) t6) F
               (Z_to_bv 64 0x14266c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (B + 4 * ia)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 (Z_to_bv 64 103) (Z_to_bv 64 e) (Z_to_bv 64 (B + 4 * ir)) s7 s8 s9 s10 (Z_to_bv 64 (B + 4 * iz)) t3 (Z_to_bv 64 103) t5 t6) F
        (Z_to_bv 64 0x142608) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs1.kr_b_072 ())). Qed.



Open Scope Z_scope.
Lemma ztb_9k k : Z_to_bv 64 (Z.shiftl (Z.land (4 * k) 18446744073709551615) 1 + Z.shiftr (4 * k) 2) = Z_to_bv 64 (9 * k).
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs1.kr_b_073 ())). Qed.
Lemma landW_sub_add_inner a b c : Z.land (Z.land a 18446744073709551615 - b + c) 18446744073709551615 = Z.land (a - b + c) 18446744073709551615.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs1.kr_b_074 ())). Qed.
Lemma max0_idiom y : -2 ^ 63 <= y < 2 ^ 63 ->
  Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? y + 9223372036854775808)) 18446744073709551615) (Z.land y 18446744073709551615)
  = Z.land (Z.max 0 y) 18446744073709551615.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs1.kr_b_075 ())). Qed.
Lemma ztb_landW x : Z_to_bv 64 (Z.land x 18446744073709551615) = Z_to_bv 64 x.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs1.kr_b_076 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Lemma fmtE1b0_walk : forall (ra sp gp tp t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s3 s8 s9 s10 s11 t6 : word)
   (F : bvmap 5 word) fc m (B ia iz ir e p p1 tc : Z) (ws : list word) (cw ct cg : word) (jB : list byte),
  mem_inv rsegs m -> u32arr rsegs m B ws -> (0 <= ia <= iz)%Z -> (iz <= Z.of_nat (length ws))%Z -> (Z.of_nat (length ws) <= 128)%Z ->
  (0 <= ir <= 122)%Z -> (B + 4 * Z.of_nat (length ws) < 2 ^ 63)%Z -> limbs_ok ws ia iz -> (-1200 < e < 1200)%Z -> (9 <= p <= 20)%Z ->
  (0 <= p1 <= p + 1200)%Z -> (tc = 101 \/ tc = 102)%Z ->
  (iz = ia \/ exists w, nth_error ws (Z.to_nat (iz - 1)) = Some w /\ bv_unsigned w <> 0%Z) ->
  rw_cells rsegs m (bv_unsigned s0 + -496) [C8 cw; C8 ct; CB 8 jB; C8 (Z_to_bv 64 0); C8 cg] ->
  (B + 4 * Z.of_nat (length ws) <= bv_unsigned s0 - 544)%Z -> (bv_unsigned s0 < 2 ^ 63)%Z ->
  evt rsegs (fun ms' => exists (j p2 : Z) a4' a5',
      (0 <= j <= 9)%Z /\ p2 = Z.min p1 (Z.max 0 (9 * (iz - ir - 1) + (if (tc =? 102)%Z then 0 else e) - j)) /\
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (B + 4 * ia)) (Z_to_bv 64 (-1)) (Z_to_bv 64 2147483647)
                    (Z_to_bv 64 (p2 + 1 + Z.b2z (0 <? p2)))%Z (Z_to_bv 64 70) a4' a5' a6 a7
                    (Z_to_bv 64 p2) s3 cg (Z_to_bv 64 e) (Z_to_bv 64 (B + 4 * ir))
                    (Z_to_bv 64 (B + 4 * iz)) (Z_to_bv 64 (Z.land tc 18446744073709551583)) (Z_to_bv 64 p2) s10 (Z_to_bv 64 p2)
                    (Z_to_bv 64 0) (Z_to_bv 64 tc) (Z_to_bv 64 0) t6) F
               (Z_to_bv 64 0x142750) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (B + 4 * ia)) (Z_to_bv 64 (4 * (iz - ir))) (Z_to_bv 64 p) a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 p1) s3 (Z_to_bv 64 103) (Z_to_bv 64 e) (Z_to_bv 64 (B + 4 * ir))
                    (Z_to_bv 64 (B + 4 * iz)) s8 s9 s10 s11 (Z_to_bv 64 0) (Z_to_bv 64 tc) (Z_to_bv 64 0) t6) F
        (Z_to_bv 64 0x14266c) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs2.kr_b_077 ())). Qed.




Open Scope Z_scope.
Lemma lor48 d : 0 <= d <= 9 -> Z.lor d 48 = d + 48.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs2.kr_b_078 ())). Qed.
Lemma div10_magic64 x : 0 <= x < 2 ^ 64 -> Z.shiftr (Z.shiftr (x * 14757395258967641293) 64) 3 = x / 10.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs2.kr_b_079 ())). Qed.
Close Scope Z_scope.

Open Scope Z_scope.
Lemma swrap32_mod x : bv_swrap 32 x = bv_swrap 32 (x mod 2 ^ 64).
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs2.kr_b_080 ())). Qed.
Lemma abs_idiom e : -2 ^ 31 < e < 2 ^ 31 ->
  bv_swrap 32 (Z.lxor (Z.land e 18446744073709551615)
                 (Z.land (bv_swrap 32 (Z.shiftr (bv_swrap 32 (Z.land e 18446744073709551615)) 31)) 18446744073709551615)
               - Z.land (bv_swrap 32 (Z.shiftr (bv_swrap 32 (Z.land e 18446744073709551615)) 31)) 18446744073709551615)
  = Z.abs e.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs2.kr_b_081 ())). Qed.
Close Scope Z_scope.

(* [comment removed for export] *)
Open Scope Z_scope.
Lemma div10_form x : 0 <= x < 2 ^ 64 ->
  Z.shiftr (Z.land (Z.shiftr (x * 14757395258967641293) 64) 18446744073709551615) 3 = x / 10.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs2.kr_b_082 ())). Qed.
Lemma digit_form x : 0 <= x < 2 ^ 31 ->
  Z.lor (Z.land (bv_swrap 32 (x - x / 10 * 10)) 18446744073709551615) 48 = x mod 10 + 48.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs2.kr_b_083 ())). Qed.
Close Scope Z_scope.

Open Scope Z_scope.
Lemma sign_form e : -2 ^ 62 <= e < 2 ^ 62 ->
  Z.land (Z.shiftr (Z.land e 18446744073709551615) 62) 2 + 43 = (if e <? 0 then 45 else 43).
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs2.kr_b_084 ())). Qed.
Close Scope Z_scope.
Ltac fix_sb :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?c)) _) => change (Z_to_le_bytes 1 c) with [Z_to_bv 8 c]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?v))) _) =>
    change (le1 (Z_to_bv 64 v)) with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 v))]; rewrite (unsigned_small64 v) by lia; mem_after_store
  end.
(* [comment removed for export] *)
Ltac it10 := zstep; zstep; zstep; zstep; rewrite div10_form by lia; zstep; zstep; zstep; rewrite digit_form by lia; zstep; fix_sb; zstep; zstep.

(* [comment removed for export] *)
Definition isdigb (b : byte) : Prop := (48 <= bv_unsigned b <= 57)%Z.
Ltac to_tail s0 TAIL DG nd ds :=
    setreg 14%Z (bv_unsigned s0 - 405 - Z.of_nat nd)%Z;
    lazymatch goal with FR : rw_cells _ ?mX _ _ |- _ =>
      eapply (TAIL nd ds); try eassumption; [cbn; lia | cbn; lia | repeat constructor; apply DG; lia |
        apply (cells_reshape _ _ _ _ FR); [ cbn [cells_bytes cbytes Nat.sub]; rewrite ?firstn_firstn; cbn [Nat.min]; rewrite <- ?app_assoc; reflexivity
                                         | cbn; rewrite ?firstn_length_le by lia; repeat split; reflexivity ] ] end.

Lemma estr_walk : forall (ra sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s3 s10 t6 : word)
   (F : bvmap 5 word) fc m (B ia iz ir e p2 l0 : Z) (cg : word) (ebuf0 : list byte),
  mem_inv rsegs m -> (-1200 < e < 1200)%Z -> (0 <= p2 <= 1220)%Z -> (1 <= l0 <= 1230)%Z -> (bv_unsigned s0 < 2 ^ 63)%Z -> (1024 <= bv_unsigned s0)%Z ->
  rw_cells rsegs m (bv_unsigned s0 + -417) [CB 12 ebuf0] ->
  evt rsegs (fun ms' => exists (ne : nat) (eb ds : list byte) (sg : Z) a4' a6' t0' t1' t2' m',
      (4 <= ne <= 6)%nat /\ length eb = ne /\ eb = Z_to_bv 8 101 :: Z_to_bv 8 sg :: ds /\ (sg = 43 \/ sg = 45)%Z /\ Forall isdigb ds /\
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (B + 4 * ia)) (Z_to_bv 64 (-1)) (Z_to_bv 64 2147483647)
                    (Z_to_bv 64 l0) (Z_to_bv 64 (Z.of_nat ne)) a4' (Z_to_bv 64 (2147483647 - l0)) a6' (Z_to_bv 64 (bv_unsigned s0 - 405 - Z.of_nat ne))
                    (Z_to_bv 64 p2) s3 cg (Z_to_bv 64 e) (Z_to_bv 64 (B + 4 * ir))
                    (Z_to_bv 64 (B + 4 * iz)) (Z_to_bv 64 69) (Z_to_bv 64 p2) s10 (Z_to_bv 64 p2)
                    (Z_to_bv 64 0) (Z_to_bv 64 101) (Z_to_bv 64 0) t6) F
               (Z_to_bv 64 0x142834) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned s0 + -417, bv_unsigned s0 + -405)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' (bv_unsigned s0 + -417) [CB (12 - ne) (firstn (12 - ne) ebuf0); CB ne eb])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (B + 4 * ia)) (Z_to_bv 64 (-1)) (Z_to_bv 64 2147483647)
                    (Z_to_bv 64 l0) (Z_to_bv 64 70) a4 a5 a6 a7
                    (Z_to_bv 64 p2) s3 cg (Z_to_bv 64 e) (Z_to_bv 64 (B + 4 * ir))
                    (Z_to_bv 64 (B + 4 * iz)) (Z_to_bv 64 69) (Z_to_bv 64 p2) s10 (Z_to_bv 64 p2)
                    (Z_to_bv 64 0) (Z_to_bv 64 101) (Z_to_bv 64 0) t6) F
        (Z_to_bv 64 0x142750) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0069 ()) [] (Mh_0069_blobs2.kr_b_085 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fmtE1t_walk : forall (ra sp gp tp t0 t1 t2 s0 a0 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t4 t6 : word)
   (F : bvmap 5 word) fc m (B ia e l0 x3 pl : Z) (ct cg ns pfx : word) (jB : list byte),
  mem_inv rsegs m -> (1 <= l0 <= 1300)%Z -> (0 <= x3 <= 1300)%Z -> (0 <= pl <= 1)%Z -> (-1200 < e < 1200)%Z ->
  rw_cells rsegs m (bv_unsigned s0 + -496) [C8 (Z_to_bv 64 1); C8 ct; CB 8 jB; C8 (Z_to_bv 64 0); C8 cg; C8 ns; C8 pfx; C8 (Z_to_bv 64 pl)] ->
  (bv_unsigned s0 < 2 ^ 63)%Z -> (1024 <= bv_unsigned s0)%Z ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (B + 4 * ia)) (Z_to_bv 64 1) (Z_to_bv 64 (2147483647 - pl)) (Z_to_bv 64 (l0 + x3)) (Z_to_bv 64 x3) a4 a5 a6 a7
                    s2 s3 s4 (Z_to_bv 64 pl) s6 s7 s8 s9 (Z_to_bv 64 (pl + (l0 + x3))) s11 (Z_to_bv 64 0) t4 (Z_to_bv 64 0) t6) F
               (Z_to_bv 64 0x1428ec) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned s0 + -488, bv_unsigned s0 + -448)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' (bv_unsigned s0 + -496) [C8 (Z_to_bv 64 1); C8 a7; CB 8 jB; C8 (Z_to_bv 64 0); C8 cg; C8 (Z_to_bv 64 0); C8 pfx; C8 (Z_to_bv 64 pl)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (B + 4 * ia)) a0 (Z_to_bv 64 2147483647) (Z_to_bv 64 l0) (Z_to_bv 64 x3) a4 a5 a6 a7
                    s2 s3 s4 (Z_to_bv 64 e) s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) t4 (Z_to_bv 64 0) t6) F
        (Z_to_bv 64 0x142834) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs2.kr_b_086 ())). Qed.

(* [comment removed for export] *)
Lemma fmtE1f_walk : forall (ra sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s3 s10 t6 : word)
   (F : bvmap 5 word) fc m (B ia iz ir e p2 l0 : Z) (cg : word),
  (-1200 < e < 1200)%Z -> (0 <= p2 <= 1220)%Z -> (1 <= l0 <= 1230)%Z ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (B + 4 * ia)) (Z_to_bv 64 (-1)) (Z_to_bv 64 2147483647)
                    (Z_to_bv 64 l0) (Z_to_bv 64 (Z.max 0 e)) a4 a5 a6 a7
                    (Z_to_bv 64 p2) s3 cg (Z_to_bv 64 e) (Z_to_bv 64 (B + 4 * ir))
                    (Z_to_bv 64 (B + 4 * iz)) (Z_to_bv 64 70) (Z_to_bv 64 p2) s10 (Z_to_bv 64 p2)
                    (Z_to_bv 64 0) (Z_to_bv 64 102) (Z_to_bv 64 0) t6) F
               (Z_to_bv 64 0x142834) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (B + 4 * ia)) (Z_to_bv 64 (-1)) (Z_to_bv 64 2147483647)
                    (Z_to_bv 64 l0) (Z_to_bv 64 70) a4 a5 a6 a7
                    (Z_to_bv 64 p2) s3 cg (Z_to_bv 64 e) (Z_to_bv 64 (B + 4 * ir))
                    (Z_to_bv 64 (B + 4 * iz)) (Z_to_bv 64 70) (Z_to_bv 64 p2) s10 (Z_to_bv 64 p2)
                    (Z_to_bv 64 0) (Z_to_bv 64 102) (Z_to_bv 64 0) t6) F
        (Z_to_bv 64 0x142750) fc None m (seg_rom rsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) [] (Mh_0069_blobs2.kr_b_087 ())). Qed.

Section E1.
Variables (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 s8 s9 s10 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (B ia iz ir e p pl : Z) (ws : list word) (cg pfx : word) (ns : Z) (jB ebuf0 : list byte).
Hypotheses (MI : mem_inv rsegs m) (AR : u32arr rsegs m B ws) (Hia : (0 <= ia < iz)%Z) (Hiz : (iz <= Z.of_nat (length ws))%Z)
           (HL : (Z.of_nat (length ws) <= 128)%Z) (Hir : (0 <= ir <= 122)%Z) (HB : (B + 4 * Z.of_nat (length ws) < 2 ^ 63)%Z)
           (LOK : limbs_ok ws ia iz) (Re : (-1200 < e < 1200)%Z) (Rp : (9 <= p <= 20)%Z) (Rpl : (0 <= pl <= 1)%Z)
           (FRA : rw_cells rsegs m (bv_unsigned s0 + -496) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 103); CB 8 jB; C8 (Z_to_bv 64 0); C8 cg; C8 (Z_to_bv 64 ns); C8 pfx; C8 (Z_to_bv 64 pl)])
           (FRE : rw_cells rsegs m (bv_unsigned s0 + -417) [CB 12 ebuf0])
           (HBS : (B + 4 * Z.of_nat (length ws) <= bv_unsigned s0 - 544)%Z) (HS0 : (bv_unsigned s0 < 2 ^ 63)%Z) (HS1 : (1024 <= bv_unsigned s0)%Z).

Definition stE1 : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (B + 4 * ia)) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 p) s3 (Z_to_bv 64 103) (Z_to_bv 64 e) (Z_to_bv 64 (B + 4 * ir)) s7 s8 s9 s10 (Z_to_bv 64 (B + 4 * iz)) t3 (Z_to_bv 64 103) t5 t6) F
     (Z_to_bv 64 0x142608) fc None m (seg_rom rsegs).

(* [comment removed for export] *)
Lemma fmtE1F_walk : fsty e p = true ->
  evt rsegs (fun ms' => exists (iz' j p2 : Z) (t0' t1' t2' a4' a5' a6' a7' : word) m',
      (ia <= iz' <= iz)%Z /\ (forall k w, (iz' <= k < iz)%Z -> nth_error ws (Z.to_nat k) = Some w -> bv_unsigned w = 0%Z) /\
      (iz' = ia \/ exists w, nth_error ws (Z.to_nat (iz' - 1)) = Some w /\ bv_unsigned w <> 0%Z) /\ (0 <= j <= 9)%Z /\
      p2 = Z.min (p - 1 - e) (Z.max 0 (9 * (iz' - ir - 1) - j)) /\
      let l := (p2 + 1 + Z.b2z (0 <? p2) + Z.max 0 e)%Z in
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (B + 4 * ia)) (Z_to_bv 64 1) (Z_to_bv 64 (2147483647 - pl)) (Z_to_bv 64 l) (Z_to_bv 64 (Z.max 0 e))
                    a4' a5' a6' a7' (Z_to_bv 64 p2) s3 cg (Z_to_bv 64 pl) (Z_to_bv 64 (B + 4 * ir)) (Z_to_bv 64 (B + 4 * iz')) (Z_to_bv 64 70) (Z_to_bv 64 p2)
                    (Z_to_bv 64 (pl + l)) (Z_to_bv 64 p2) (Z_to_bv 64 0) (Z_to_bv 64 102) (Z_to_bv 64 0) t6) F
               (Z_to_bv 64 0x1428ec) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned s0 + -488, bv_unsigned s0 + -448)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' (bv_unsigned s0 + -496) [C8 (Z_to_bv 64 1); C8 a7'; CB 8 jB; C8 (Z_to_bv 64 0); C8 cg; C8 (Z_to_bv 64 0); C8 pfx; C8 (Z_to_bv 64 pl)])
    stE1.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) ["E1"] (Mh_0069_blobs2.kr_b_088 ())). Qed.

(* [comment removed for export] *)
Lemma fmtE1E_walk : fsty e p = false ->
  evt rsegs (fun ms' => exists (iz' j p2 : Z) (ne : nat) (eb ds : list byte) (sg : Z) (t0' t1' t2' a4' a5' a6' : word) m',
      (ia <= iz' <= iz)%Z /\ (forall k w, (iz' <= k < iz)%Z -> nth_error ws (Z.to_nat k) = Some w -> bv_unsigned w = 0%Z) /\
      (iz' = ia \/ exists w, nth_error ws (Z.to_nat (iz' - 1)) = Some w /\ bv_unsigned w <> 0%Z) /\ (0 <= j <= 9)%Z /\
      p2 = Z.min (p - 1) (Z.max 0 (9 * (iz' - ir - 1) + e - j)) /\
      (4 <= ne <= 6)%nat /\ length eb = ne /\ eb = Z_to_bv 8 101 :: Z_to_bv 8 sg :: ds /\ (sg = 43 \/ sg = 45)%Z /\ Forall isdigb ds /\
      let l := (p2 + 1 + Z.b2z (0 <? p2) + Z.of_nat ne)%Z in
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (B + 4 * ia)) (Z_to_bv 64 1) (Z_to_bv 64 (2147483647 - pl)) (Z_to_bv 64 l) (Z_to_bv 64 (Z.of_nat ne))
                    a4' a5' a6' (Z_to_bv 64 (bv_unsigned s0 - 405 - Z.of_nat ne)) (Z_to_bv 64 p2) s3 cg (Z_to_bv 64 pl) (Z_to_bv 64 (B + 4 * ir)) (Z_to_bv 64 (B + 4 * iz'))
                    (Z_to_bv 64 69) (Z_to_bv 64 p2) (Z_to_bv 64 (pl + l)) (Z_to_bv 64 p2) (Z_to_bv 64 0) (Z_to_bv 64 101) (Z_to_bv 64 0) t6) F
               (Z_to_bv 64 0x1428ec) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned s0 + -488, bv_unsigned s0 + -448); (bv_unsigned s0 + -417, bv_unsigned s0 + -405)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' (bv_unsigned s0 + -496) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (bv_unsigned s0 - 405 - Z.of_nat ne)); CB 8 jB; C8 (Z_to_bv 64 0); C8 cg; C8 (Z_to_bv 64 0); C8 pfx; C8 (Z_to_bv 64 pl)]
      /\ rw_cells rsegs m' (bv_unsigned s0 + -417) [CB (12 - ne) (firstn (12 - ne) ebuf0); CB ne eb])
    stE1.
Proof.
ltac2:(KReplay.run1 (kr_t_WaWkFmtE ()) ["E1"] (Mh_0069_blobs2.kr_b_089 ())). Qed.
End E1.

End WaWkFmtE.
