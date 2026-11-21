(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the vDSO; the model's fetch-failure and unmodeled answers. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_FrmKeep () := "C46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init9Datatypes3fstK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv3Sem5is_x0C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics5Riscv3Sem9with_regsC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes6option00K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4rsetK47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes4bool00C4ELinuxProcessSemantics5Riscv3Sem7with_pcC4ELinuxProcessSemantics5Riscv3Sem9with_resvC4ELinuxProcessSemantics5Riscv3Sem:with_fregsc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM=fc_with_fregsC13~~~C4ELinuxProcessSemantics5Riscv3Sem4fsetC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv3Sem7nan_boxc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM7fc_fsetC13~~~C4ELinuxProcessSemantics5Riscv3Sem6fwriteI4ELinuxProcessSemantics5Riscv5Instr4ffmt00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics5Riscv3Sem6c_resvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3eqbK47Corelib4Init9Datatypes6option02c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM<fc_with_resvC13~~~C4ELinuxProcessSemantics5Riscv3Sem:inval_resvC4ELinuxProcessSemantics5Riscv3Sem6accrueC4ELinuxProcessSemantics5Riscv3Fpu;fflags_bitsC56Stdlib6ZArith6BinInt1Z3lorI4ELinuxProcessSemantics5Riscv3Fpu6fflags00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FPSteps8frm_zeroC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FPStepsDfp_fflags_bits_rangeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FPStepsBfp_frm_zero_accrueC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM9fc_accrueC13~~~C47Corelib4Init5Logic8eq_ind_rc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM>csr_frm_unsafeC13~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv3Sem9slice_getC45stdpp9bitvector;definitions5bv_orK4ELinuxProcessSemantics5Riscv3Sem3eff02c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM6eff_fzC13~~~C47Corelib4Init9Datatypes3orbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FPStepsDfp_frm_zero_slice0_5C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM7fc_rsetC13~~~K4ELinuxProcessSemantics5Riscv3Sem3eff01C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics5Riscv3Sem8exec_csrC45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics5Riscv3Sem9slice_setC4ELinuxProcessSemantics5Riscv3Sem9with_fcsrC47Corelib4Init9Datatypes4andbK47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics5Riscv5Instr5csrop00I4ELinuxProcessSemantics5Riscv3Sem3eff00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5instr01C4ELinuxProcessSemantics5Riscv3Sem4c_pcC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions9bv_concatC4ELinuxProcessSemantics5Riscv7Prelude4sextK4ELinuxProcessSemantics5Riscv5Instr5instr02K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv5Instr5instr04C4ELinuxProcessSemantics5Riscv3Sem4rgetK4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv3Sem<branch_takenK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv3Sem3eff07K4ELinuxProcessSemantics5Riscv5Instr5instr07C45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics5Riscv3Sem3eff08C4ELinuxProcessSemantics5Riscv3Sem5low32c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM=fc_inval_resvC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv5Instr5instr0;C4ELinuxProcessSemantics5Riscv3Sem5alu32K4ELinuxProcessSemantics5Riscv5Instr5instr0<K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr0>K4ELinuxProcessSemantics5Riscv5Instr5instr0?K4ELinuxProcessSemantics5Riscv5Instr5instr0BC4ELinuxProcessSemantics5Riscv3Sem7mul_divK4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv5Instr5instr0DC4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv3Sem3eff06K4ELinuxProcessSemantics5Riscv5Instr5instr0EK4ELinuxProcessSemantics5Riscv5Instr5instr0FC4ELinuxProcessSemantics5Riscv3Sem7amo_valK4ELinuxProcessSemantics5Riscv5Instr5instr0GC4ELinuxProcessSemantics5Riscv3SemAcsr_write_illegalK4ELinuxProcessSemantics5Riscv3Sem3eff03C46Stdlib4Bool4Bool=negb_true_iffc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM:csr_writesC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM;exec_csr_fzC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0HK4ELinuxProcessSemantics5Riscv5Instr5instr0IK4ELinuxProcessSemantics5Riscv5Instr5instr0JC4ELinuxProcessSemantics5Riscv3Sem4fgetK4ELinuxProcessSemantics5Riscv5Instr5instr0KC4ELinuxProcessSemantics5Riscv3Sem:resolve_rmC4ELinuxProcessSemantics5Riscv3Sem5freadC4ELinuxProcessSemantics5Riscv3Sem9fp_formatC4ELinuxProcessSemantics5Riscv3Fpu6fp_negC4ELinuxProcessSemantics5Riscv3Fpu6fp_fmac89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM9fz_accrueC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM9fc_fwriteC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0LC4ELinuxProcessSemantics5Riscv3Fpu6fp_addC4ELinuxProcessSemantics5Riscv3Fpu6fp_subC4ELinuxProcessSemantics5Riscv3Fpu6fp_mulC4ELinuxProcessSemantics5Riscv3Fpu6fp_divK4ELinuxProcessSemantics5Riscv5Instr5instr0MC4ELinuxProcessSemantics5Riscv3Fpu7fp_sqrtK4ELinuxProcessSemantics5Riscv5Instr5instr0NC4ELinuxProcessSemantics5Riscv3Sem7unbox_sC4ELinuxProcessSemantics5Riscv3Sem8sgnj_valK4ELinuxProcessSemantics5Riscv5Instr5instr0OC4ELinuxProcessSemantics5Riscv3Fpu9fp_minmaxK4ELinuxProcessSemantics5Riscv5Instr5instr0PC4ELinuxProcessSemantics5Riscv3Fpu5fp_eqC4ELinuxProcessSemantics5Riscv3Fpu5fp_ltC4ELinuxProcessSemantics5Riscv3Fpu5fp_leK4ELinuxProcessSemantics5Riscv5Instr5instr0QC4ELinuxProcessSemantics5Riscv3Fpu:fp_convertC4ELinuxProcessSemantics5Riscv3Fpu9fp_of_intC4ELinuxProcessSemantics5Riscv3Fpu9fp_to_intK4ELinuxProcessSemantics5Riscv5Instr5instr0RK4ELinuxProcessSemantics5Riscv5Instr5instr0SC4ELinuxProcessSemantics5Riscv3Fpu8fp_classc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM>instr_frm_safeC13~~~C4ELinuxProcessSemantics5Riscv3Sem4execI4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w1I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00I4ELinuxProcessSemantics5Riscv5Instr5msize00K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv5Instr5aluop00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0@K4ELinuxProcessSemantics5Riscv5Instr5instr0AI4ELinuxProcessSemantics5Riscv5Instr5mulop00I4ELinuxProcessSemantics5Riscv5Instr6awidth00K4ELinuxProcessSemantics5Riscv5Instr6awidth01K4ELinuxProcessSemantics5Riscv5Instr6awidth02C4ELinuxProcessSemantics5Riscv3Sem2w0I4ELinuxProcessSemantics5Riscv5Instr5amoop00I47Corelib4Init5Logic3and00K4ELinuxProcessSemantics5Riscv5Instr4ffmt01K4ELinuxProcessSemantics5Riscv5Instr4ffmt02I4ELinuxProcessSemantics5Riscv5Instr5fmaop00I4ELinuxProcessSemantics5Riscv3Fpu5rmode00I4ELinuxProcessSemantics5Riscv5Instr6fariop00I4ELinuxProcessSemantics5Riscv5Instr6fsgnop00I4ELinuxProcessSemantics5Riscv5Instr9fminmaxop00I4ELinuxProcessSemantics5Riscv5Instr6fcmpop00I4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty00I4ELinuxProcessSemantics5Riscv5Instr6fmvdir00K4ELinuxProcessSemantics5Riscv5Instr6fmvdir01K4ELinuxProcessSemantics5Riscv5Instr6fmvdir02I47Corelib4Init9Datatypes4list00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics5Riscv3Sem3eff04K4ELinuxProcessSemantics5Riscv3Sem3eff05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;width_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics5Riscv3Sem7eff_indK47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib7Numbers7BinNums1N00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM=word_frm_safeC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM7exec_fzC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM9interp_fzC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init9Datatypes8BoolSpec00K47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType>seg_executableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC56Stdlib6NArith6BinNat1N6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsAseg_ov_read_bytesc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM?find_segment_InC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<code_read_ovC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le4c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRMAcode_read_ov_noneC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_halfC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_half_ovC4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le2C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_half_anyC4ELinuxProcessSemantics5Riscv7Prelude4bitsc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRMAfetch_half_any_eqC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_tailC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBsegment_read_bytesI47Corelib4Init5Logic2ex00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRMBfind_segment_rangeC13~~~K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9code_readc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM=code_read_segC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM5scan1C13~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM5ok_atC13~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op201I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM5scan2C13~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM;scan1_soundC13~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppI47Corelib4Init5Logic2or00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM>fetch_word_segC13~~~C56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM>fetch_tail_segC13~~~C46Stdlib6ZArith4Zdiv:Zminus_modc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM;scan2_soundC13~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failurec89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM>decode_exec_fzC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRMBfetch_word_ov_noneC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRMAfetch_tail_any_eqC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@fetch_byte_trapsI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM7step_fzC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim:msteps_indC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6fp_csrC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmKeep3FRM9msteps_fzC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FRM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition csr_frm_unsafe (writes : bool) (csr : bv 12) : bool :=
  writes && ((bv_unsigned csr =? 2) || (bv_unsigned csr =? 3)).
Definition csr_writes (op : csrop) (nz : bool) : bool := match op with CSR_RW => true | _ => nz end.
Definition instr_frm_safe (i : instr) : bool :=
  match i with
  | Csr op rd rs1 csr => negb (csr_frm_unsafe (csr_writes op (negb (is_x0 rs1))) csr)
  | CsrI op rd uimm csr => negb (csr_frm_unsafe (csr_writes op (negb (Z.eqb (bv_unsigned uimm) 0))) csr)
  | _ => true
  end.
Definition word_frm_safe (w : bv 32) : bool :=
  match decode_any w with Some (i, _) => instr_frm_safe i | None => true end.

(* [comment removed for export] *)
Fixpoint eff_fz (e : eff) : Prop :=
  match e with
  | EDone c => frm_zero (c_fcsr c)
  | ELoad n a k => forall v, eff_fz (k v)
  | EStore n a v k => eff_fz k
  | _ => True
  end.

(* [comment removed for export] *)
Lemma fc_rset r v c : c_fcsr (rset r v c) = c_fcsr c.
Proof. unfold rset. destruct (is_x0 r); [reflexivity|]. destruct c; reflexivity. Qed.
Lemma fc_with_pc v c : c_fcsr (with_pc v c) = c_fcsr c.
Proof. destruct c; reflexivity. Qed.
Lemma fc_with_resv v c : c_fcsr (with_resv v c) = c_fcsr c.
Proof. destruct c; reflexivity. Qed.
Lemma fc_with_regs f c : c_fcsr (with_regs f c) = c_fcsr c.
Proof. destruct c; reflexivity. Qed.
Lemma fc_with_fregs f c : c_fcsr (with_fregs f c) = c_fcsr c.
Proof. destruct c; reflexivity. Qed.
Lemma fc_fset r v c : c_fcsr (fset r v c) = c_fcsr c.
Proof. unfold fset. apply fc_with_fregs. Qed.
Lemma fc_fwrite fmt r v c : c_fcsr (fwrite fmt r v c) = c_fcsr c.
Proof. unfold fwrite. destruct fmt; apply fc_fset. Qed.
Lemma fc_inval_resv a c : c_fcsr (inval_resv a c) = c_fcsr c.
Proof. unfold inval_resv. destruct (c_resv c) as [r0|]; [destruct (bv_unsigned r0 =? bv_unsigned a); [apply fc_with_resv| reflexivity]| reflexivity]. Qed.
Lemma fc_accrue fl c : c_fcsr (accrue fl c) = Z_to_bv 32 (Z.lor (bv_unsigned (c_fcsr c)) (fflags_bits fl)).
Proof. destruct c; reflexivity. Qed.
Lemma fz_accrue fl c : frm_zero (c_fcsr c) -> frm_zero (c_fcsr (accrue fl c)).
Proof. intros H. rewrite fc_accrue. apply fp_frm_zero_accrue; [apply fp_fflags_bits_range| exact H]. Qed.

Ltac fz_core FZ :=
  repeat first [ exact FZ
               | rewrite fc_rset | rewrite fc_with_pc | rewrite fc_with_resv | rewrite fc_with_regs | rewrite fc_fset
               | rewrite fc_fwrite | rewrite fc_inval_resv | apply fz_accrue ].

Ltac fz_tree FZ :=
  repeat first [ lazymatch goal with
                 | |- eff_fz (match ?x with _ => _ end) => destruct x
                 | |- eff_fz ((match ?x with _ => _ end) _) => destruct x
                 | |- eff_fz (EDone _) => cbn [eff_fz]
                 | |- eff_fz (ELoad _ _ _) => cbn [eff_fz]; intros ?
                 | |- eff_fz (EStore _ _ _ _) => cbn [eff_fz]
                 | |- eff_fz (exec_csr _ _ _ _ _ _) => fail
                 | |- eff_fz _ => exact I
                 | |- frm_zero (c_fcsr (match ?x with _ => _ end)) => destruct x
                 | |- frm_zero _ => progress (fz_core FZ)
                 end ].

(* [comment removed for export] *)
Lemma exec_csr_fz op rd operand writes csr c :
  frm_zero (c_fcsr c) -> csr_frm_unsafe writes csr = false -> eff_fz (exec_csr op rd operand writes csr c).
Proof.
  intros FZ SF. unfold exec_csr, csr_slice. cbv zeta. unfold csr_frm_unsafe in SF.
  destruct (Z.eqb_spec (bv_unsigned csr) 1) as [E1|N1].
  - cbn [eff_fz]. rewrite fc_rset. destruct writes; [| exact FZ]. apply fp_frm_zero_slice0_5. exact FZ.
  - destruct (Z.eqb_spec (bv_unsigned csr) 2) as [E2|N2].
    + destruct writes; [cbn in SF; rewrite ?E2 in SF; cbn in SF; discriminate|]. cbn [eff_fz]. rewrite fc_rset. exact FZ.
    + destruct (Z.eqb_spec (bv_unsigned csr) 3) as [E3|N3]; [| exact I].
      destruct writes; [cbn in SF; rewrite ?E3 in SF; cbn in SF; discriminate|]. cbn [eff_fz]. rewrite fc_rset. exact FZ.
Qed.

Lemma exec_fz (sz : word) (i : instr) (c : core) :
  frm_zero (c_fcsr c) -> instr_frm_safe i = true -> eff_fz (exec sz i c).
Proof.
  intros FZ SF. destruct i; cbv beta iota zeta delta [exec load_val store_val]; try (fz_tree FZ).
  -   cbn [instr_frm_safe csr_writes] in SF. apply negb_true_iff in SF. apply exec_csr_fz; [fz_core FZ| exact SF].
  -   cbn [instr_frm_safe csr_writes] in SF. apply negb_true_iff in SF. apply exec_csr_fz; [fz_core FZ| exact SF].
Qed.

(* [comment removed for export] *)
Lemma interp_fz segs : forall e m rep, eff_fz e -> interp_eff_accesses segs e m = MachineOk rep -> frm_zero (c_fcsr (fst (@access_value _ rep))).
Proof.
  induction e as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m rep FZ H; cbn [interp_eff_accesses] in H; try discriminate.
  - injection H as <-. exact FZ.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|destruct (range_meets_vvar segs a (width_bytes n)); discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r| | ] eqn:E; try discriminate.
    injection H as <-. cbn [access_value fst]. exact (IH _ m r (FZ _) E).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r| | ] eqn:E; try discriminate.
    injection H as <-. cbn [access_value fst]. exact (IH _ r FZ E).
Qed.

(* [comment removed for export] *)
Lemma decode_exec_fz segs st w rep :
  frm_zero (ms_fcsr st) -> word_frm_safe w = true -> decode_exec_accesses segs st w = MachineOk rep -> frm_zero (ms_fcsr (@access_value _ rep)).
Proof.
  intros FZ SF H. unfold decode_exec_accesses in H. unfold word_frm_safe in SF.
  destruct (is_ecall w); [injection H as <-; exact FZ|].
  destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
  destruct (interp_eff_accesses _ _) as [r| | ] eqn:E; try discriminate.
  pose proof (interp_fz segs _ _ r (exec_fz (Z_to_bv 64 isz) i (Core (ms_regs st) (ms_fregs st) (ms_pc_val st) (ms_fcsr st) (ms_resv st)) FZ SF) E) as FZ'.
  destruct (@access_value _ r) as [c m'] eqn:Er. cbv beta iota zeta in H. injection H as <-. cbn [access_value ms_fcsr fst] in *. exact FZ'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma find_segment_In : forall l a n seg, find_segment l a n = Some seg -> In seg l.
Proof.
  induction l as [|s l IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (_ && _); [injection H as <-; left; reflexivity| right; exact (IH _ _ _ H)].
Qed.
Lemma find_segment_range : forall l a n seg, find_segment l a n = Some seg ->
  Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction l as [|s l IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.leb_spec (Z.of_N (seg_base s)) a) as [L1|L1]; destruct (Z.leb_spec (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [L2|L2]; cbn [andb] in H;
    first [injection H as <-; split; assumption | exact (IH _ _ _ H)].
Qed.

Section Generic.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis no_wx : forall seg, In seg segs -> seg_executable seg && seg_writable seg = false.

Lemma code_read_ov_none m a n : code_read_ov segs m a n = None.
Proof.
  unfold code_read_ov. destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:E; [|reflexivity].
  rewrite (no_wx seg (find_segment_In _ _ _ _ E)). reflexivity.
Qed.
Lemma fetch_word_ov_none m a : fetch_word_ov segs m a = None.
Proof. unfold fetch_word_ov. rewrite code_read_ov_none. destruct (negb _); reflexivity. Qed.
Lemma fetch_half_any_eq m a : fetch_half_any segs m a = fetch_half segs a.
Proof. unfold fetch_half_any. destruct (fetch_half segs a); [reflexivity|]. unfold fetch_half_ov. rewrite code_read_ov_none. reflexivity. Qed.
Lemma fetch_tail_any_eq m a : fetch_tail_any segs m a = fetch_tail segs a.
Proof. unfold fetch_tail_any, fetch_tail. rewrite !fetch_half_any_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma code_read_seg a n bs : code_read segs a n = Some bs ->
  exists seg, In seg segs /\ seg_executable seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + Z.of_N n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  unfold code_read. destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:E; [|discriminate].
  destruct (seg_executable seg) eqn:X; [|discriminate]. intros _. exists seg.
  split; [exact (find_segment_In _ _ _ _ E)|]. split; [exact X|]. exact (find_segment_range _ _ _ _ E).
Qed.
Lemma fetch_word_seg a w : fetch_word segs a = Some w ->
  bv_unsigned a mod 2 = 0 /\ exists seg, In seg segs /\ seg_executable seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + 4 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  unfold fetch_word. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  destruct (code_read segs a 4) as [bs|] eqn:C; [|discriminate]. intros _. split; [exact E|]. exact (code_read_seg a 4 bs C).
Qed.
Lemma fetch_tail_seg a w : fetch_tail segs a = Some w ->
  bv_unsigned a mod 2 = 0 /\ exists seg, In seg segs /\ seg_executable seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + 2 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  unfold fetch_tail. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  unfold fetch_half at 1. destruct (code_read segs a 2) as [bs|] eqn:C; [|discriminate]. intros _. split; [exact E|]. exact (code_read_seg a 2 bs C).
Qed.

(* [comment removed for export] *)
Definition ok_at (a : Z) : bool :=
  (match fetch_word segs (Z_to_bv 64 a) with Some w => word_frm_safe w | None => true end)
  && (match fetch_tail segs (Z_to_bv 64 a) with Some w => word_frm_safe w | None => true end).
Fixpoint scan1 (f : nat) (a : Z) : bool := match f with O => true | S f' => ok_at a && scan1 f' (a + 2) end.
Fixpoint scan2 (g f : nat) (a : Z) : bool := match g with O => true | S g' => scan1 f a && scan2 g' f (a + 2 * Z.of_nat f) end.

Lemma scan1_sound : forall f a0, scan1 f a0 = true -> forall a, a0 <= a < a0 + 2 * Z.of_nat f -> (a - a0) mod 2 = 0 -> ok_at a = true.
Proof.
  induction f as [|f IH]; intros a0 H a Ha Hm; [cbn [Z.of_nat] in Ha; lia|].
  cbn [scan1] in H. apply andb_true_iff in H as [H0 H1].
  destruct (Z.eq_dec a a0) as [->|NE]; [exact H0|].
  apply (IH (a0 + 2) H1); [lia|]. replace (a - (a0 + 2)) with (a - a0 + (-1) * 2) by lia. rewrite Z.mod_add by lia. exact Hm.
Qed.
Lemma scan2_sound : forall g f a0, scan2 g f a0 = true -> forall a, a0 <= a < a0 + 2 * Z.of_nat f * Z.of_nat g -> (a - a0) mod 2 = 0 -> ok_at a = true.
Proof.
  induction g as [|g IH]; intros f a0 H a Ha Hm; [cbn [Z.of_nat] in Ha; lia|].
  cbn [scan2] in H. apply andb_true_iff in H as [H0 H1].
  destruct (Z_lt_le_dec a (a0 + 2 * Z.of_nat f)) as [LT|GE].
  - exact (scan1_sound f a0 H0 a ltac:(lia) Hm).
  - apply (IH f (a0 + 2 * Z.of_nat f) H1); [lia|]. replace (a - (a0 + 2 * Z.of_nat f)) with (a - a0 + (- Z.of_nat f) * 2) by lia.
    rewrite Z.mod_add by lia. exact Hm.
Qed.

(* [comment removed for export] *)
Theorem fetch_safe_of_scan (xlo xsz : Z) (g f : nat) :
  (forall seg, In seg segs -> seg_executable seg = true -> Z.of_N (seg_base seg) = xlo /\ Z.of_N (seg_size seg) = xsz) ->
  xlo mod 2 = 0 -> xsz <= 2 * Z.of_nat f * Z.of_nat g -> scan2 g f xlo = true ->
  forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> word_frm_safe w = true.
Proof.
  intros XS XE COV SC a w H.
  assert (R : bv_unsigned a mod 2 = 0 /\ xlo <= bv_unsigned a < xlo + xsz).
  { destruct H as [H|H]; [destruct (fetch_word_seg a w H) as (E & seg & IN & X & B1 & B2)| destruct (fetch_tail_seg a w H) as (E & seg & IN & X & B1 & B2)];
      destruct (XS seg IN X) as (EB & ES); split; [exact E| lia| exact E| lia]. }
  destruct R as (EA & RA).
  assert (OK : ok_at (bv_unsigned a) = true).
  { apply (scan2_sound g f xlo SC); [lia|]. rewrite Zminus_mod, EA, XE. reflexivity. }
  unfold ok_at in OK. rewrite Z_to_bv_bv_unsigned in OK. apply andb_true_iff in OK as [O1 O2].
  destruct H as [H|H]; [rewrite H in O1; exact O1| rewrite H in O2; exact O2].
Qed.

(* [comment removed for export] *)
Hypothesis fetch_safe : forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> word_frm_safe w = true.

Theorem step_fz : forall s s', RiscvSemantics.step segs s = MachineOk s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof.
  intros s s' H FZ. unfold RiscvSemantics.step, step_accesses in H.
  destruct (fetch_word segs (ms_pc s)) as [w|] eqn:F1.
  - destruct (decode_exec_accesses segs s w) as [r| | ] eqn:E; try discriminate. cbn [drop_access_report] in H. injection H as <-.
    exact (decode_exec_fz segs s w r FZ (fetch_safe _ _ (or_introl F1)) E).
  - rewrite fetch_word_ov_none, fetch_tail_any_eq in H.
    destruct (fetch_tail segs (ms_pc s)) as [w|] eqn:F2.
    + destruct (decode_exec_accesses segs s w) as [r| | ] eqn:E; try discriminate. cbn [drop_access_report] in H. injection H as <-.
      exact (decode_exec_fz segs s w r FZ (fetch_safe _ _ (or_intror F2)) E).
    + exfalso. unfold fetch_failure in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

Theorem msteps_fz : forall s s', msteps segs s s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof.
  intros s s' H. induction H as [ms| ms ms' ms'' P ST MS IH]; intros FZ; [exact FZ|].
  apply IH. exact (step_fz ms ms' ST FZ).
Qed.

(* [comment removed for export] *)
Corollary msteps_fz_mkst (fx fx' : FPState) R R' pc pc' M M' :
  msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs)) -> frm_zero (@fp_csr fx) -> frm_zero (@fp_csr fx').
Proof. intros MS FZ. exact (msteps_fz _ _ MS FZ). Qed.
End Generic.
End FRM.
