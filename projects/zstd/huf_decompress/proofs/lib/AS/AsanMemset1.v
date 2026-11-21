(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (A_exit0, A_exit2, A_exit6 and 11 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import MemsetLib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanMemset_code.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanMemset1 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare3at_C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib2AS9MemsetLib5cbyteC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib2AS9MemsetLib5cfillC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib8ms_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib2AS8PropExec4btgtC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib2AS8PropExec4c_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib2AS7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib2AS7SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;step_beq_tkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_jalr_x0C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List2InC47Corelib4Init5Logic3notK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01c59OSSVerify5KrLib2AS;AsanMemset1>asanreflect_fxC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib2AS?AsanMemset_code7ms_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgGTgt_huf_decompress_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8e98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_000C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib2AS?AsanMemset_code6Do_000C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib7ms_clobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib2AS8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib2AS8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib=ms_v_add_at_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec;step_add_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC59OSSVerify5KrLib2AS8PropExec9step_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec:getr_otherC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib2AS9MemsetLib5cf_sbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib2AS8PropExec<step_bltu_tkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib=ms_agree_reflC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib2AS9MemsetLib<ms_agree_updC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib2AS9MemsetLib>asanreflect_fxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8e9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_004C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_004C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanMemset12L2C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ea0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_008C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_008C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ea4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_00cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_00cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ea8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_010C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_010C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8eacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_014C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_014C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib2AS8PropExec<step_bltu_ftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanMemset12L6C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8eb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_018C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_018C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8eb4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_01cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_01cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8eb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_020C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_020C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ebcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_024C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_024C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ec0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_028C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_028C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ec4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_02cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_02cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanMemset12L8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ec8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_030C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_030C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8eccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_034C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_034C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ed0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_038C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_038C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ed4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_03cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_03cC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib2AS8PropExec6v_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib3c32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9step_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9step_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib2AS8PropExec5v_luiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8step_luiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_andiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare4at_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_andi_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib;ms_v_sub_ZZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec;step_sub_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7v_mulhuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib9mulhu_c32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib@ms_step_mulhu_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib9wleb4_c32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib5cf_swC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanMemset12LBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ed8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_040C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_040C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8edcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_044C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_044C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ee0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_048C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_048C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ee4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_04cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_04cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ee8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_050C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_050C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8eecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_054C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_054C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ef0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_058C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_058C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ef4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_05cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_05cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8ef8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_060C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_060C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8efcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_064C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_064C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_068C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_068C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_06cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_06cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_070C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_070C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_074C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_074C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanMemset12LCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_078C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_078C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_07cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_07cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_080C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_080C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_084C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_084C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_088C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_088C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_08cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_08cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanMemset12LDC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib2AS9MemsetLib;ms_v_addi_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_addi_atC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_090C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_090C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_094C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_094C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_098C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_098C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_09cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_09cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f3cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0c0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0c0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib3c64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib4c32hC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib:slli32_c32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_slli_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_srliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib;srli32_c32hC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_srli_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4v_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib6or_c64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib=ms_step_or_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0c4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0c4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0c8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0c8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0d4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init5Logic8iff_reflC59OSSVerify5KrLib2AS9MemsetLib9wleb8_c64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare7at_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib6ms_covC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib6ms_inbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool:orb_true_rC47Corelib7Classes?RelationClasses?Equivalence_PERC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms?eq_proper_proxyC59OSSVerify5KrLib2AS9MemsetLib;ms_inb_trueC1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_Prop?or_iff_morphismC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses9iff_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib4Bool4Bool>eq_true_iff_eqC46Stdlib4Bool4Bool;orb_false_rC59OSSVerify5KrLib2AS9MemsetLib;ms_cov_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib9cfill_extC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib2AS9MemsetLib>ms_agree_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<RefMemcpyLib:runs_transC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib2AS9MemsetLib5cf_sdC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK46Stdlib9micromega5Tauto8GFormula09C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0ecC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib2AS?AsanMemset_code7W_a8f88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Fo_0f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanMemset_code6Do_0f0C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_Reflexive".
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
(* [comment removed for export] *)
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
(* [comment removed for export] *)
#[local] Ltac cond :=
  rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
(* [comment removed for export] *)
#[local] Ltac pclits :=
  repeat match goal with
         | |- context [Z_to_bv 64 (ms_base + ?o)%Z] => wlit_replace (Z_to_bv 64 (ms_base + o)%Z)
         end.
(* [comment removed for export] *)
#[local] Ltac stepat L F D vv tac :=
  chain_step; [reflexivity | eapply L with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl].

Section Walk.
  Variable mem0 : word -> option byte.
  Variables d cv ret : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok MSEGS mem0 d (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ret.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
  #[local] Abbreviation PC o := (Z_to_bv 64 (ms_base + o)).

  (* [comment removed for export] *)
  #[local] Ltac msb F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sb MSEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | lia | lia]
      | step_simpl].
  #[local] Ltac msw F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sw MSEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | apply wleb4_c32
        | lia | lia]
      | step_simpl].
  #[local] Ltac msd F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sd MSEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | apply wleb8_c64
        | lia | lia]
      | step_simpl].
  (* [comment removed for export] *)
  #[local] Ltac mret := stepret Fo_0f4 Do_0f4 ret ltac:(rwH; reflexivity).
  (* [comment removed for export] *)
  #[local] Ltac post := repeat split; gres; rwH; try reflexivity; solve_ms_agree.

  (* [comment removed for export] *)
  Definition L2 : list (Z * Z) := [(n-1,1); (0,1)]%Z.
  Definition L6 : list (Z * Z) := [(n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.
  Definition L8 : list (Z * Z) := [(n-4,1); (3,1); (n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma A_exit0 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (n = 0)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF []) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_tk Fo_000 Do_000 ltac:(cond).          (* [comment removed for export] *)
      mret.
      apply mst_refl.
    - post.
  Qed.

  Lemma A_exit2 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (1 <= n <= 2)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L2) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).          (* [comment removed for export] *)
      msb Fo_004 Do_004 0%Z.                         (* [comment removed for export] *)
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).  (* [comment removed for export] *)
      stepn Fo_00c Do_00c.                           (* [comment removed for export] *)
      msb Fo_010 Do_010 (n-1)%Z.                     (* [comment removed for export] *)
      stepb_tk Fo_014 Do_014 ltac:(cond).          (* [comment removed for export] *)
      mret.
      apply mst_refl.
    - post.
  Qed.

  Lemma A_exit6 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (3 <= n <= 6)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L6) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).
      msb Fo_004 Do_004 0%Z.
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      stepn Fo_00c Do_00c.
      msb Fo_010 Do_010 (n-1)%Z.
      stepb_ft Fo_014 Do_014 ltac:(cond).
      msb Fo_018 Do_018 1%Z.                         (* [comment removed for export] *)
      msb Fo_01c Do_01c 2%Z.                         (* [comment removed for export] *)
      stepn Fo_020 Do_020.                           (* [comment removed for export] *)
      msb Fo_024 Do_024 (n-3)%Z.                     (* [comment removed for export] *)
      msb Fo_028 Do_028 (n-2)%Z.                     (* [comment removed for export] *)
      stepb_tk Fo_02c Do_02c ltac:(cond).          (* [comment removed for export] *)
      mret.
      apply mst_refl.
    - post.
  Qed.

  Lemma A_exit8 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (7 <= n <= 8)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L8) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).
      msb Fo_004 Do_004 0%Z.
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      stepn Fo_00c Do_00c.
      msb Fo_010 Do_010 (n-1)%Z.
      stepb_ft Fo_014 Do_014 ltac:(cond).
      msb Fo_018 Do_018 1%Z.
      msb Fo_01c Do_01c 2%Z.
      stepn Fo_020 Do_020.
      msb Fo_024 Do_024 (n-3)%Z.
      msb Fo_028 Do_028 (n-2)%Z.
      stepb_ft Fo_02c Do_02c ltac:(cond).
      msb Fo_030 Do_030 3%Z.                         (* [comment removed for export] *)
      stepn Fo_034 Do_034.                           (* [comment removed for export] *)
      msb Fo_038 Do_038 (n-4)%Z.                     (* [comment removed for export] *)
      stepb_tk Fo_03c Do_03c ltac:(cond).          (* [comment removed for export] *)
      mret.
      apply mst_refl.
    - post.
  Qed.

  Lemma A_cont : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (9 <= n)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' (PC 0x40) (CF L8) rom)
      /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = cv /\ getr regs' 12 = Z_to_bv 64 n
      /\ getr regs' 13 = at_ d n /\ getr regs' 15 = Z_to_bv 64 9 /\ getr regs' 1 = ret
      /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).
      msb Fo_004 Do_004 0%Z.
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      stepn Fo_00c Do_00c.
      msb Fo_010 Do_010 (n-1)%Z.
      stepb_ft Fo_014 Do_014 ltac:(cond).
      msb Fo_018 Do_018 1%Z.
      msb Fo_01c Do_01c 2%Z.
      stepn Fo_020 Do_020.
      msb Fo_024 Do_024 (n-3)%Z.
      msb Fo_028 Do_028 (n-2)%Z.
      stepb_ft Fo_02c Do_02c ltac:(cond).
      msb Fo_030 Do_030 3%Z.
      stepn Fo_034 Do_034.
      msb Fo_038 Do_038 (n-4)%Z.
      stepb_ft Fo_03c Do_03c ltac:(cond).          (* [comment removed for export] *)
      apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Section Aligned.
    Variables k n1 : Z.
    Hypothesis Hk : (0 <= k <= 3)%Z.
    Hypothesis Hn1 : (n - k - 3 <= n1 <= n - k)%Z.
    Hypothesis Hkv : v_andi (v_subw (Z_to_bv 64 0) d) 3 = Z_to_bv 64 k.
    Hypothesis Hn1v : v_andi (Z_to_bv 64 (n - k)) (-4) = Z_to_bv 64 n1.

    Definition LB : list (Z * Z) := ((k+n1-4,4) :: (k,4) :: L8)%Z.
    Definition LC : list (Z * Z) := ((k+n1-8,4) :: (k+n1-12,4) :: (k+8,4) :: (k+4,4) :: LB)%Z.
    Definition LD (s4 : Z) : list (Z * Z) :=
      ((k+n1-16,4) :: (k+n1-20,4) :: (k+n1-24,4) :: (k+n1-28,4)
        :: (k+24,4) :: (k+20,4) :: (k+16,4) :: (k+12,4) :: LC)%Z.

    #[local] Ltac blockB :=
      stepn Fo_040 Do_040;                           (* [comment removed for export] *)
      stepn Fo_044 Do_044;                           (* [comment removed for export] *)
      stepn Fo_048 Do_048;                           (* [comment removed for export] *)
      stepiv Fo_04c Do_04c (Z_to_bv 64 k) ltac:(gres; rwH; imm_norm; rewrite at_0; exact Hkv);   (* [comment removed for export] *)
      stepn Fo_050 Do_050;                           (* [comment removed for export] *)
      stepiv Fo_054 Do_054 (Z_to_bv 64 (n - k)) ltac:(gres; rwH; apply ms_v_sub_ZZ; lia);          (* [comment removed for export] *)
      stepiv Fo_058 Do_058 (at_ d k) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia);  (* [comment removed for export] *)
      stepn Fo_05c Do_05c;                           (* [comment removed for export] *)
      stepiv Fo_060 Do_060 (Z_to_bv 64 n1) ltac:(gres; rwH; imm_norm; exact Hn1v);              (* [comment removed for export] *)
      stepat ms_step_mulhu_at Fo_064 Do_064 (c32 cv) ltac:(gres; rwH; apply mulhu_c32; unorm; reflexivity);  (* [comment removed for export] *)
      msw Fo_068 Do_068 k;                           (* [comment removed for export] *)
      stepiv Fo_06c Do_06c (at_ d (k + n1)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; reflexivity);  (* [comment removed for export] *)
      msw Fo_070 Do_070 (k + n1 - 4)%Z.              (* [comment removed for export] *)

    Lemma B_exit : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
      getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (n1 < 9)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' ret (CF LB) rom)
        /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
    Proof.
      intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockB.
        stepb_tk Fo_074 Do_074 ltac:(cond).        (* [comment removed for export] *)
        mret.
        apply mst_refl.
      - post.
    Qed.

    Lemma B_cont : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
      getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (9 <= n1)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' (PC 0x78) (CF LB) rom)
        /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
        /\ getr regs' 13 = at_ d (k + n1) /\ getr regs' 14 = Z_to_bv 64 n1 /\ getr regs' 1 = ret
        /\ ms_agree regs regs'.
    Proof.
      intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockB.
        stepb_ft Fo_074 Do_074 ltac:(cond).        (* [comment removed for export] *)
        apply mst_refl.
      - post.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    #[local] Ltac blockC :=
      msw Fo_078 Do_078 (k + 4)%Z;                   (* [comment removed for export] *)
      msw Fo_07c Do_07c (k + 8)%Z;                   (* [comment removed for export] *)
      stepn Fo_080 Do_080;                           (* [comment removed for export] *)
      msw Fo_084 Do_084 (k + n1 - 12)%Z;             (* [comment removed for export] *)
      msw Fo_088 Do_088 (k + n1 - 8)%Z.              (* [comment removed for export] *)

    Lemma C_exit : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
      getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (12 <= n1)%Z -> (n1 < 25)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' ret (CF LC) rom)
        /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
    Proof.
      intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockC.
        stepb_tk Fo_08c Do_08c ltac:(cond).        (* [comment removed for export] *)
        mret.
        apply mst_refl.
      - post.
    Qed.

    Lemma C_cont : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
      getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (25 <= n1)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' (PC 0x90) (CF LC) rom)
        /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
        /\ getr regs' 13 = at_ d (k + n1) /\ getr regs' 14 = Z_to_bv 64 n1 /\ getr regs' 1 = ret
        /\ ms_agree regs regs'.
    Proof.
      intros regs H10 H11 H12 H13 H14 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockC.
        stepb_ft Fo_08c Do_08c ltac:(cond).        (* [comment removed for export] *)
        apply mst_refl.
      - post.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Section D.
      Variable s4 : Z.
      Hypothesis Hs4 : (s4 = 0 \/ s4 = 4)%Z.
      Hypothesis Hs4v : v_andi (at_ d k) 4 = Z_to_bv 64 s4.

      #[local] Ltac blockD :=
        msw Fo_090 Do_090 (k + 12)%Z;                (* [comment removed for export] *)
        msw Fo_094 Do_094 (k + 16)%Z;                (* [comment removed for export] *)
        msw Fo_098 Do_098 (k + 20)%Z;                (* [comment removed for export] *)
        msw Fo_09c Do_09c (k + 24)%Z;                (* [comment removed for export] *)
        stepiv Fo_0a0 Do_0a0 (Z_to_bv 64 s4) ltac:(gres; rwH; imm_norm; exact Hs4v);          (* [comment removed for export] *)
        stepn Fo_0a4 Do_0a4;                         (* [comment removed for export] *)
        stepiv Fo_0a8 Do_0a8 (Z_to_bv 64 (s4 + 24)) ltac:(gres; rwH; imm_norm; apply ms_v_addi_Z; lia);  (* [comment removed for export] *)
        stepiv Fo_0ac Do_0ac (Z_to_bv 64 (n1 - s4 - 24)) ltac:(gres; rwH; rewrite ms_v_sub_ZZ by lia; f_equal; lia);  (* [comment removed for export] *)
        msw Fo_0b0 Do_0b0 (k + n1 - 28)%Z;           (* [comment removed for export] *)
        msw Fo_0b4 Do_0b4 (k + n1 - 24)%Z;           (* [comment removed for export] *)
        msw Fo_0b8 Do_0b8 (k + n1 - 20)%Z;           (* [comment removed for export] *)
        msw Fo_0bc Do_0bc (k + n1 - 16)%Z.           (* [comment removed for export] *)

      Lemma D_exit : forall regs,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z -> (n1 - s4 - 24 < 32)%Z ->
        exists regs',
          msteps MSEGS (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' ret (CF (LD s4)) rom)
          /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
      Proof.
        intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
        eexists. split.
        - blockD.
          stepb_tk Fo_0c0 Do_0c0 ltac:(cond).      (* [comment removed for export] *)
          mret.
          apply mst_refl.
        - post.
      Qed.

      Lemma D_cont : forall regs,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z -> (32 <= n1 - s4 - 24)%Z ->
        exists regs',
          msteps MSEGS (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' (PC 0xc4) (CF (LD s4)) rom)
          /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
          /\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24) /\ getr regs' 15 = Z_to_bv 64 (s4 + 24)
          /\ getr regs' 1 = ret /\ ms_agree regs regs'.
      Proof.
        intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
        eexists. split.
        - blockD.
          stepb_ft Fo_0c0 Do_0c0 ltac:(cond).      (* [comment removed for export] *)
          apply mst_refl.
        - post.
      Qed.

      (* [comment removed for export] *)
      (* [comment removed for export] *)
      (* [comment removed for export] *)

      Lemma E_run : forall regs L,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 14 = Z_to_bv 64 (n1 - s4 - 24) -> getr regs 15 = Z_to_bv 64 (s4 + 24) -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z ->
        exists regs',
          msteps MSEGS (mkst regs (PC 0xc4) (CF L) rom) (mkst regs' (PC 0xd8) (CF L) rom)
          /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d (k + s4 + 24) /\ getr regs' 12 = c64 cv
          /\ getr regs' 13 = Z_to_bv 64 31 /\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24)
          /\ getr regs' 1 = ret /\ ms_agree regs regs'.
      Proof.
        intros regs L H10 H11 H12 H14 H15 H1 Hn9 Hn1'. pose proof (u64_range d) as Hd. pclits.
        eexists. split.
        - stepiv Fo_0c4 Do_0c4 (c32h cv) ltac:(gres; rwH; imm_norm; apply slli32_c32).             (* [comment removed for export] *)
          stepiv Fo_0c8 Do_0c8 (at_ d (k + s4 + 24)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).  (* [comment removed for export] *)
          stepiv Fo_0cc Do_0cc (c32 cv) ltac:(gres; rwH; imm_norm; apply srli32_c32h);             (* [comment removed for export] *)
          stepat ms_step_or_at Fo_0d0 Do_0d0 (c64 cv) ltac:(gres; rwH; apply or_c64).                 (* [comment removed for export] *)
          stepn Fo_0d4 Do_0d4.                       (* [comment removed for export] *)
          apply mst_refl.
        - post.
      Qed.
    End D.
  End Aligned.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[local] Ltac ms_cov_eq :=
    intros i Hi; rewrite !ms_cov_cons;
    match goal with |- _ = ?rhs => match rhs with context [ms_cov ?L i] => destruct (ms_cov L i) end end;
    rewrite ?orb_true_r, ?orb_false_r; [reflexivity|];
    apply eq_true_iff_eq; rewrite !orb_true_iff, !ms_inb_true; lia.

  (* [comment removed for export] *)
  Lemma loop_run : forall (q : nat) regs L a r,
    getr regs 10 = at_ d 0 -> getr regs 11 = at_ d a -> getr regs 12 = c64 cv ->
    getr regs 13 = Z_to_bv 64 31 -> getr regs 14 = Z_to_bv 64 r -> getr regs 1 = ret ->
    (0 <= a)%Z -> (a + r <= n)%Z ->
    (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0xd8) (CF L) rom)
                   (mkst regs' (PC 0xf4) (CF ((a, 32 * (Z.of_nat q + 1))%Z :: L)) rom)
      /\ getr regs' 10 = at_ d 0 /\ getr regs' 1 = ret /\ ms_agree regs regs'.
  Proof.
    induction q as [|q IH]; intros regs L a r H10 H11 H12 H13 H14 H1 Ha Har Hq;
      pose proof (u64_range d) as Hd; pclits.
    - (* [comment removed for export] *)
      eexists. split.
      + msd Fo_0d8 Do_0d8 a.                         (* [comment removed for export] *)
        msd Fo_0dc Do_0dc (a + 8)%Z.                 (* [comment removed for export] *)
        msd Fo_0e0 Do_0e0 (a + 16)%Z.                (* [comment removed for export] *)
        msd Fo_0e4 Do_0e4 (a + 24)%Z.                (* [comment removed for export] *)
        stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).  (* [comment removed for export] *)
        stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).               (* [comment removed for export] *)
        stepb_ft Fo_0f0 Do_0f0 ltac:(cond).        (* [comment removed for export] *)
        replace (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z
          with (CF ((a, 32 * (Z.of_nat 0 + 1))%Z :: L)) by (apply cfill_ext; ms_cov_eq).
        apply mst_refl.
      + post.
    - eapply (runs_trans MSEGS _
                (fun rg => mkst rg (PC 0xd8) (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z rom)
                (fun rg => getr rg 10 = at_ d 0 /\ getr rg 11 = at_ d (a + 32) /\ getr rg 12 = c64 cv
                           /\ getr rg 13 = Z_to_bv 64 31 /\ getr rg 14 = Z_to_bv 64 (r - 32) /\ getr rg 1 = ret
                           /\ ms_agree regs rg)).
      + cbv beta. pclits. eexists. split.
        * msd Fo_0d8 Do_0d8 a.
          msd Fo_0dc Do_0dc (a + 8)%Z.
          msd Fo_0e0 Do_0e0 (a + 16)%Z.
          msd Fo_0e4 Do_0e4 (a + 24)%Z.
          stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).
          stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
          stepb_tk Fo_0f0 Do_0f0 ltac:(cond).      (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R10 & R11 & R12 & R13 & R14 & R1 & AG).
        destruct (IH r1 ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z (a + 32)%Z (r - 32)%Z
                    R10 R11 R12 R13 R14 R1 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
        exists r2. split.
        * replace (CF ((a, 32 * (Z.of_nat (S q) + 1))%Z :: L))
            with (CF ((a + 32, 32 * (Z.of_nat q + 1))%Z :: ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z))
            by (apply cfill_ext; ms_cov_eq).
          revert RUN. pclits. intros RUN. exact RUN.
        * repeat split; try assumption. eapply ms_agree_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ret_run : forall regs (M : word -> option byte),
    getr regs 1 = ret ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0xf4) M rom) (mkst regs' ret M rom)
      /\ regs' = regs.
  Proof.
    intros regs M H1. pclits. eexists. split.
    - mret. apply mst_refl.
    - reflexivity.
  Qed.

End Walk.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
