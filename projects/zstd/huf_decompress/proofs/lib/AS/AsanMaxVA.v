(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (10 recorded proofs replaced by written proofs (step_or_at, step_and_at, step_sll_at and 7 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec CatExec CatSim SeqExec AgentLib AsanStartLoops.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanMaxVA () := "C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr09K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib2AS9AsanMaxVA2W0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5instr01c59OSSVerify5KrLib2AS9AsanMaxVA2W1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2W2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2W3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2W4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:c59OSSVerify5KrLib2AS9AsanMaxVA2W5C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5instr0;c59OSSVerify5KrLib2AS9AsanMaxVA2W6C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2W7C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2W8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2W9C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W10C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W11C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W12C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03c59OSSVerify5KrLib2AS9AsanMaxVA3W13C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c59OSSVerify5KrLib2AS9AsanMaxVA3W14C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W15C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W16C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W17C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W18C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W19C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W20C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W21C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W22C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W23C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W24C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W25C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W26C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W27C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08c59OSSVerify5KrLib2AS9AsanMaxVA3W28C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop06c59OSSVerify5KrLib2AS9AsanMaxVA3W29C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W30C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c59OSSVerify5KrLib2AS9AsanMaxVA3W31C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02c59OSSVerify5KrLib2AS9AsanMaxVA3W32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W33C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W34C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W35C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W36C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W37C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W38C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0Bc59OSSVerify5KrLib2AS9AsanMaxVA3W39C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01c59OSSVerify5KrLib2AS9AsanMaxVA3W40C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=c59OSSVerify5KrLib2AS9AsanMaxVA3W41C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib2AS9AsanMaxVA3W42C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W43C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3W44C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC45stdpp9bitvector;definitions4BvWfC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4v_orC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC59OSSVerify5KrLib2AS8PropExec7step_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA>asanreflect_fxC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib2AS8PropExec5v_andC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8step_andC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_sllC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8step_sllC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9step_subwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z<testbit_trueK46Stdlib9micromega6VarMap1t01C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z=testbit_falseC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z9div_smallK47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00c59OSSVerify5KrLib2AS9AsanMaxVA7topfullC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z=shiftr_nonnegC47Corelib4Init9Datatypes3orbC46Stdlib6ZArith:ZArith_dec8Z_le_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z8min_specI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool:orb_true_rC56Stdlib6ZArith6BinInt1Z;shiftr_specC56Stdlib6ZArith6BinInt1Z8lor_specK46Stdlib9micromega5Tauto8GFormula06C46Stdlib6ZArith:ZArith_dec8Z_lt_decC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z=ones_spec_lowC56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z9bits_inj'C59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z;le_lt_transC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib2AS8PropExec;Z_lor_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AgentLib7u64_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_srliC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA<topfull_initC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA<topfull_stepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA7u_orsrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA;topfull_allC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqI47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc59OSSVerify5KrLib2AS9AsanMaxVA:maxva_postC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_srli_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec;step_lui_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec:getr_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA:step_or_atC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib2AS8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec=step_addiw_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_slli_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec;step_add_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA7smear47C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_xori_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA;step_and_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec;step_sub_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_mulC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec;step_mul_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA<step_subw_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_addi_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA;step_sll_atC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphK59OSSVerify5KrLib2AS6CatSim6msteps02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanStartLoops:v_addi_litC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Peano2ltC59OSSVerify5KrLib2AS8PropExec5v_addC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltc59OSSVerify5KrLib2AS9AsanMaxVA2E0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2D0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2E1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2D1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2E2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2D2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2E3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2D3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2E4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2D4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2E5C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2D5C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00c59OSSVerify5KrLib2AS9AsanMaxVA2E6C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2D6C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2E7C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2D7C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2E8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2D8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2E9C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA2D9C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E10C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D10C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E11C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D11C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E12C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D12C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E13C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D13C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E14C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D14C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E15C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D15C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E16C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D16C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E17C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D17C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E18C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D18C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E19C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D19C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E20C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D20C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E21C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D21C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E22C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D22C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E23C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D23C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E24C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D24C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E25C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D25C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E26C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D26C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E27C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D27C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E28C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D28C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E29C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D29C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E30C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D30C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E31C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D31C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E33C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D33C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E34C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D34C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E35C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D35C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E36C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D36C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E37C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D37C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E38C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D38C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E39C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D39C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E40C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D40C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E41C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D41C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E42C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D42C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E43C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D43C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3E44C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9AsanMaxVA3D44C1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W0 : bv 32 := 0x00155593.
Lemma D0 : decode_any W0 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210p1001:p4p710p8g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j13Tg004Uj15Tg0053j11Tg005Qj32Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR1g00;[R0'BR2#AR3g00<9#9R4P1P0g00<mg00=YR5#0R6#3R7#5R8%37#1g00>>R932%07#1=289%35#0#5%15;29C8%06#1C7,62R634R9P3P3%:3P1g00>ZP0g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E0 : is_ecall W0 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W1 : bv 32 := 0x55555637.
Lemma D1 : decode_any W1 = Some (Lui 12 349525, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2CTg0028j1BTg002Zj1:Tg003Kj11Tg0040j12Tg004Uj16Tg0053j13Tg005Qj34Tg00ADj29Tg006`j47Tg007@j28Tg007bj35j1ATg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2=Tg009ij2>Tg00:Gj3;Tf0#2#1p=0g00:oR0g00;[R1'CR2#BR3g00B0#:R4P0P1g00=YR5#1R6#2R7#6%05#1#3g00>>R534%17R7#1#6%07#0#0#0#0#0#0#2#3;45'9%16#3C7,82R635R5P3P3%A3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2'=1>56=542d3;o"). Qed.
Lemma E1 : is_ecall W1 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W2 : bv 32 := 0x333336b7.
Lemma D2 : decode_any W2 = Some (Lui 13 209715, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j12Tg005Qj33Tg00ADj28Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00Bd#9R4P0P1g00=YR5#0R6#1R7#5%15#0R5#1#2g00>>R833%07#0#5%05#1#1#0#0#1#1#0#0#1#1#0#0#1#1#2;38'8%06#2C7,62R634R8P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=86=442d3>o"). Qed.
Lemma E2 : is_ecall W2 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W3 : bv 32 := 0x0f0f1737.
Lemma D3 : decode_any W3 = Some (Lui 14 61681, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j12Tg005Qj33Tg00ADj28Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00CX#9R4P0P1g00=YR5#0R6#1R7#5%15#1R5#0#2g00>>R833%07#0#5%15#0#0#0#0#1#1#1#1#0#0#0#1#2;38'8%06#2C7,62R634R8P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=86=442d3>o"). Qed.
Lemma E3 : is_ecall W3 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W4 : bv 32 := 0x010107b7.
Lemma D4 : decode_any W4 = Some (Lui 15 4112, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2CTg0028j1BTg002Zj1:Tg003Kj12Tg0040j10Tg004Uj16Tg0053j13Tg005Qj34Tg00ADj29Tg006`j47Tg007@j28Tg007bj35j1ATg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2=Tg009ij2>Tg00:Gj3;Tf0#2#2p=1g00:oR0g00;[R1'CR2#BR3g00DL#:R4P0P1g00=YR5#2R6#0R7#6%05#0#0#3g00>>R534%17#6%26R6#2#1#1#0#1#1#3;45'9%36C7,82R635R5P3P3%A3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2'=1>56=542d3;o"). Qed.
Lemma E4 : is_ecall W4 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W5 : bv 32 := 0x00b56533.
Lemma D5 : decode_any W5 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj11Tg0040j14Tg004Uj1:Tg0053j10Tg005Qj32Tg00E@j47Tg006`j46Tg007@j25Tg007bj33j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00El#8R4P0P1g00F`g00=Y#1R5#4R6#:R7%16#0g00>>R832R9P9%46#0=278C7%15#0C6,52R533R8P3P3%93P0g00>ZP1g00?KC@,?2P4P5E;R5g00?dR4g00@DR2'<1=85=342d3>o"). Qed.
Lemma E5 : is_ecall W5 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W6 : bv 32 := 0x5556059b.
Lemma D6 : decode_any W6 = Some (OpImm32 11 12 1365, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j12Tg005Qj33Tg00GLj38Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00H8#9R4P0P1g00=YR5#0R6#1R7#5R8%17#2g00>>R933%15#0#0R5#2=389%55%07#1#0#1#0#1#0#1#2;3938%06#2C7,62R634R9P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E6 : is_ecall W6 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W7 : bv 32 := 0x3336861b.
Lemma D7 : decode_any W7 = Some (OpImm32 12 13 819, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj11Tg0040j10Tg004Uj15Tg0053j12Tg005Qj33Tg00GLj38Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00Hl#9R4P0P1g00=YR5#1R6#0#5R7%05#1R5#1R8#2g00>>R933%05#2=379%58%08#0#1#1#0#0#2;3938%16#2C7,62R634R9P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E7 : is_ecall W7 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W8 : bv 32 := 0xf0f7069b.
Lemma D8 : decode_any W8 = Some (OpImm32 13 14 3855, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj11Tg0040j10Tg004Uj15Tg0053j12Tg005Qj33Tg00GLj38Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00I`#9R4P0P1g00=YR5#1R6#0#5R7%05R5#1R8#0#2g00>>R933%05R5#1#2=379%18#5%05#1#1#1#1#0#0#0#0#2;3938%16#2C7,62R634R9P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E8 : is_ecall W8 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W9 : bv 32 := 0x1017871b.
Lemma D9 : decode_any W9 = Some (OpImm32 14 15 257, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j12Tg005Qj33Tg00GLj38Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00JT#9R4P0P1g00=YR5#0R6#1#5R7%15R5#1R8#0#2g00>>R933%18#2=379%05#0#5%06R6#0#0#0#0#0#1#2;3938%26C7,62R634R9P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E9 : is_ecall W9 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W10 : bv 32 := 0x00255793.
Lemma D10 : decode_any W10 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj11Tg0040j10Tg004Uj15Tg0053j12Tg005Qj33Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00KH#9R4P0P1g00<mg00=YR5#1R6#0R7#5R8%05R5#0#0#2g00>>R933%17#2=389%15#5%26;39C8%16#2C7,62R634R9P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E10 : is_ecall W10 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W11 : bv 32 := 0x00f56533.
Lemma D11 : decode_any W11 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj12Tg0040j10Tg004Uj1:Tg0053j11Tg005Qj33Tg00E@j47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00L=#8R4P0P1g00F`g00=YR5#2R6#0R7#:R8%27#1g00>>R733R9P9%05#0#0#1=387C7%26#1C6,52R634R7P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=76=442d3>o"). Qed.
Lemma E11 : is_ecall W11 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W12 : bv 32 := 0x02059793.
Lemma D12 : decode_any W12 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j12Tg005Qj33Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00M2#9R4P0P1g00Mgg00=YR5#0R6#1R7#5R8%15R5#1#1#2g00>>R933%17#2=389%05#5%06R6#0#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E12 : is_ecall W12 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W13 : bv 32 := 0x00f585b3.
Lemma D13 : decode_any W13 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj13Tg0040j10Tg004Uj1:Tg0053j11Tg005Qj32Tg00E@j47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00NS#8R4P0P1g00OHg00=YR5#3R6#0R7#:R8%07#1g00>>R732R9P9%05#0#0#1=287C7%36#1C6,52R634R7P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=76=442d3>o"). Qed.
Lemma E13 : is_ecall W13 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W14 : bv 32 := 0x02061793.
Lemma D14 : decode_any W14 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j12Tg005Qj33Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00P4#9R4P0P1g00Mgg00=YR5#0R6#1#5R7%15R5#1#1#2g00>>R833%05R5#0#2=378%55%06R6#0#0#0#2;38C8%26C7,62R634R8P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=86=442d3>o"). Qed.
Lemma E14 : is_ecall W14 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W15 : bv 32 := 0x00f60633.
Lemma D15 : decode_any W15 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj10Tg0040j11Tg004Uj1:Tg0053j12Tg005Qj33Tg00E@j47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00Pi#8R4P0P1g00OHg00=YR5#0R6#1#:R7%15R5#0#0#2g00>>R833R9P9%15#1#2=378C7%06#2C6,52R634R8P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=86=442d3>o"). Qed.
Lemma E15 : is_ecall W15 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W16 : bv 32 := 0x02069793.
Lemma D16 : decode_any W16 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j12Tg005Qj33Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00Q^#9R4P0P1g00Mgg00=YR5#0R6#1#5R7%15R5#1#1#2g00>>R833%05R5#1#2=378%55%06R6#0#0#0#2;38C8%26C7,62R634R8P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=86=442d3>o"). Qed.
Lemma E16 : is_ecall W16 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W17 : bv 32 := 0x00f686b3.
Lemma D17 : decode_any W17 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj12Tg0040j10Tg004Uj1:Tg0053j11Tg005Qj33Tg00E@j47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00RS#8R4P0P1g00OHg00=YR5#2R6#0#:R7%05R5#2#0#1g00>>R833R9P9%05#0#1=378C7%26#1C6,52R634R8P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=86=442d3>o"). Qed.
Lemma E17 : is_ecall W17 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W18 : bv 32 := 0x02071793.
Lemma D18 : decode_any W18 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j12Tg005Qj33Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00SH#9R4P0P1g00Mgg00=YR5#0R6#1#5R7%15R5#1R8#1#2g00>>R933%08#2=379%05#5%06R6#0#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E18 : is_ecall W18 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W19 : bv 32 := 0x00f70733.
Lemma D19 : decode_any W19 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj12Tg0040j10Tg004Uj1:Tg0053j11Tg005Qj33Tg00E@j47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00T=#8R4P0P1g00OHg00=YR5#2R6#0#:R7%05#0R5#2#1g00>>R833R9P9%05#1=378C7%26#1C6,52R634R8P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=86=442d3>o"). Qed.
Lemma E19 : is_ecall W19 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W20 : bv 32 := 0x00455793.
Lemma D20 : decode_any W20 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j13Tg005Qj32Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00U2#9R4P0P1g00<mg00=YR5#0R6#1R7#5R8%15R5#1#1#3g00>>R932%07#3=289%05#5%06#3R6;29C8P6C7,62R634R9P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E20 : is_ecall W20 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W21 : bv 32 := 0x00f56533.
Lemma D21 : decode_any W21 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj12Tg0040j10Tg004Uj1:Tg0053j11Tg005Qj33Tg00E@j47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00Ug#8R4P0P1g00F`g00=YR5#2R6#0R7#:R8%27#1g00>>R733R9P9%05#0#0#1=387C7%26#1C6,52R634R7P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=76=442d3>o"). Qed.
Lemma E21 : is_ecall W21 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W22 : bv 32 := 0x00855793.
Lemma D22 : decode_any W22 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j12Tg005Qj33Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00V\#9R4P0P1g00<mg00=YR5#0R6#1R7#5R8%15R5#1#1#2g00>>R933%07#2=389%05#5%06R6#0#2;39C8%26C7,62R634R9P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E22 : is_ecall W22 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W23 : bv 32 := 0x00f56533.
Lemma D23 : decode_any W23 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj12Tg0040j10Tg004Uj1:Tg0053j11Tg005Qj33Tg00E@j47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00WQ#8R4P0P1g00F`g00=YR5#2R6#0R7#:R8%27#1g00>>R733R9P9%05#0#0#1=387C7%26#1C6,52R634R7P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=76=442d3>o"). Qed.
Lemma E23 : is_ecall W23 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W24 : bv 32 := 0x01055793.
Lemma D24 : decode_any W24 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j12Tg005Qj33Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00XF#9R4P0P1g00<mg00=YR5#0R6#1R7#5R8%15R5#1#1#2g00>>R933%07#2=389%05#5%06R6#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E24 : is_ecall W24 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W25 : bv 32 := 0x00f56533.
Lemma D25 : decode_any W25 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj12Tg0040j10Tg004Uj1:Tg0053j11Tg005Qj33Tg00E@j47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00Y;#8R4P0P1g00F`g00=YR5#2R6#0R7#:R8%27#1g00>>R733R9P9%05#0#0#1=387C7%26#1C6,52R634R7P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=76=442d3>o"). Qed.
Lemma E25 : is_ecall W25 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W26 : bv 32 := 0x02055793.
Lemma D26 : decode_any W26 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j12Tg005Qj33Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00Z0#9R4P0P1g00<mg00=YR5#0R6#1R7#5R8%15R5#1#1#2g00>>R933%07#2=389%05#5%06R6#0#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E26 : is_ecall W26 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W27 : bv 32 := 0x00f56533.
Lemma D27 : decode_any W27 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj12Tg0040j10Tg004Uj1:Tg0053j11Tg005Qj33Tg00E@j47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00Ze#8R4P0P1g00F`g00=YR5#2R6#0R7#:R8%27#1g00>>R733R9P9%05#0#0#1=387C7%26#1C6,52R634R7P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=76=442d3>o"). Qed.
Lemma E27 : is_ecall W27 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W28 : bv 32 := 0xfff54513.
Lemma D28 : decode_any W28 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2CTg0028j1BTg002Zj1:Tg003Kj11Tg0040j12Tg004Uj16Tg0053j13Tg005Qj34Tg00[Zj49Tg006`j47Tg007@j28Tg007bj35j1ATg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2=Tg009ij2>Tg00:Gj3;Tf0#2#2p=0g00:oR0g00;[R1'CR2#BR3g00\F#:R4P0P1g00];g00=YR5#1R6#2R7#6%17#3g00>>R734R8P8%25R5#1#1#6%05#0#0#0#0#3;47C9%16#3C7,82R635R7P3P3%A3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2'=1>76=542d3;o"). Qed.
Lemma E28 : is_ecall W28 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W29 : bv 32 := 0x00155793.
Lemma D29 : decode_any W29 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj11Tg0040j10Tg004Uj15Tg0053j12Tg005Qj33Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00]g#9R4P0P1g00<mg00=YR5#1R6#0R7#5R8%05R9#0#0#2g00>>R:33%17#2=38:%19#5%25;3:C8%16#2C7,62R634R:P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=:6=442d3>o"). Qed.
Lemma E29 : is_ecall W29 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W30 : bv 32 := 0x00b7f5b3.
Lemma D30 : decode_any W30 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj13Tg0040j10Tg004Uj1:Tg0053j11Tg005Qj32Tg00E@j47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00^\#8R4P0P1g00_Qg00=YR5#3R6#0R7#:R8%07#1g00>>R732R9%05#0#0#1=287P9C7%36#1C6,52R634R9P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=96=442d3>o"). Qed.
Lemma E30 : is_ecall W30 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W31 : bv 32 := 0x40b50533.
Lemma D31 : decode_any W31 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj11Tg0040j14Tg004Uj1:Tg0053j10Tg005Qj32Tg00E@j47Tg006`j46Tg007@j25Tg007bj33j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00`=#8R4P0P1g00a2g00=Y#1R5#4R6#:R7%16#0g00>>R832R9P9%46#0=278C7%15#0C6,52R533R8P3P3%93P0g00>ZP1g00?KC@,?2P4P5E;R5g00?dR4g00@DR2'<1=85=342d3>o"). Qed.
Lemma E31 : is_ecall W31 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W32 : bv 32 := 0x00c575b3.
Lemma D32 : decode_any W32 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj10Tg0040j13Tg004Uj1:Tg0053j11Tg005Qj32Tg00E@j47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00a^#8R4P0P1g00_Qg00=YR5#0R6#3R7#:R8%37#1g00>>R932%07#1=289%35#0#0#1=289C7%06#1C6,52R634R9P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=96=442d3>o"). Qed.
Lemma E32 : is_ecall W32 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W33 : bv 32 := 0x00255513.
Lemma D33 : decode_any W33 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j15Tg004Uj13Tg0053j11Tg005Qj32Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00bS#9R4P0P1g00<mg00=YR5#0R6#5R7#3%07#1g00>>R732R8P8%55#0#3%16;27C8%06#1C7,62R634R7P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=76=442d3>o"). Qed.
Lemma E33 : is_ecall W33 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W34 : bv 32 := 0x00c57533.
Lemma D34 : decode_any W34 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj10Tg0040j14Tg004Uj1:Tg0053j11Tg005Qj32Tg00E@j47Tg006`j46Tg007@j25Tg007bj33j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00cH#8R4P0P1g00_Qg00=YR5#0R6#4R7#:R8%07#1g00>>R732R9P9%45#0#0#1=287C7%06#1C6,52R633R7P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=76=342d3>o"). Qed.
Lemma E34 : is_ecall W34 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W35 : bv 32 := 0x00a58533.
Lemma D35 : decode_any W35 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj11Tg0040j14Tg004Uj1:Tg0053j10Tg005Qj32Tg00E@j47Tg006`j46Tg007@j25Tg007bj33j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00d=#8R4P0P1g00OHg00=Y#1R5#4R6#:R7%16#0g00>>R832R9%46#0=278P9C7%15#0C6,52R533R9P3P3%93P0g00>ZP1g00?KC@,?2P4P5E;R5g00?dR4g00@DR2'<1=95=342d3>o"). Qed.
Lemma E35 : is_ecall W35 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W36 : bv 32 := 0x00455593.
Lemma D36 : decode_any W36 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j12Tg004Uj15Tg0053j13Tg005Qj31Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00e2#9R4P0P1g00<mg00=YR5#0R6#2R7#5R8%27#3g00>>R931%07#3=189%25#0#5%06#3R6;19C8P6C7,62R634R9P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=96=442d3>o"). Qed.
Lemma E36 : is_ecall W36 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W37 : bv 32 := 0x00b50533.
Lemma D37 : decode_any W37 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj11Tg0040j14Tg004Uj1:Tg0053j10Tg005Qj32Tg00E@j47Tg006`j46Tg007@j25Tg007bj33j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00eg#8R4P0P1g00OHg00=Y#1R5#4R6#:R7%16#0g00>>R832R9P9%46#0=278C7%15#0C6,52R533R8P3P3%93P0g00>ZP1g00?KC@,?2P4P5E;R5g00?dR4g00@DR2'<1=85=342d3>o"). Qed.
Lemma E37 : is_ecall W37 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W38 : bv 32 := 0x00d57533.
Lemma D38 : decode_any W38 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj10Tg0040j12Tg004Uj1:Tg0053j11Tg005Qj33Tg00E@j47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00f\#8R4P0P1g00_Qg00=YR5#0R6#2R7#:R8%07#1g00>>R733R9P9%25#0#2#1=387C7%06#1C6,52R634R7P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=76=442d3>o"). Qed.
Lemma E38 : is_ecall W38 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W39 : bv 32 := 0x02e50533.
Lemma D39 : decode_any W39 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj10Tg0040j12Tg004Uj1:Tg0053j11Tg005Qj33Tg00gQj47Tg006`j46Tg007@j25Tg007bj34j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00h=#8R4P0P1g00i2g00=YR5#0R6#2R7#:R8%07#1g00>>R733R9P9%25#2#0#1=387C7%06#1C6,52R634R7P3P3%93P0g00>ZP1g00?KC@,?2P4P6E;R6g00?dR4g00@DR2'<1=76=442d3>o"). Qed.
Lemma E39 : is_ecall W39 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W40 : bv 32 := 0x03855513.
Lemma D40 : decode_any W40 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj19Tg003Kj10Tg0040j11Tg004Uj15Tg0053j12Tg005Qj33Tg0064j48Tg006`j47Tg007@j26Tg007bj34j1:Tg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2;Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00i^#9R4P0P1g00<mg00=YR5#0R6#1R7#5%07#2g00>>R733R8P8%15R5#0#5%15#0#0#0#2;37C8%06#2C7,62R634R7P3P3%:3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2';1=76=442d3>o"). Qed.
Lemma E40 : is_ecall W40 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W41 : bv 32 := 0x40a0053b.
Lemma D41 : decode_any W41 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj15Tg003Kj10Tg0040j1@Tg004Uj18Tg0053j11Tg005Qj32Tg00jSj46Tg006`j47Tg007@j24Tg007bj33j19Tg008<j4?Tg008Zj2:Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00k?#5R4P0P1g00a2g00=Y#0R5#@R6#8R7%06#1g00>>R632R8g00l4=276P8C6%05#1C7,42R533R8P3P3%93P0g00>ZP1g00?KC?,:2P4P5E;R5g00?dR4g00@DR2'<1=85=342d3>o"). Qed.
Lemma E41 : is_ecall W41 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W42 : bv 32 := 0xfff00593.
Lemma D42 : decode_any W42 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2CTg0028j1BTg002Zj1:Tg003Kj12Tg0040j10Tg004Uj16Tg0053j14Tg005Qj33Tg00[Zj49Tg006`j47Tg007@j28Tg007bj35j1ATg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2=Tg009ij2>Tg00:Gj3;Tf0#0#0p=1g00:oR0g00;[R1'CR2#BR3g00lR#:R4P0P1g00OHg00=YR5#2R6#0R7#6R8%07#4g00>>R733g00l4=387%05R5#2#2#6%15#1#1#1#1#4;37C9%26#4C7,82R635R7P3P3%A3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2'=1>76=542d3;o"). Qed.
Lemma E42 : is_ecall W42 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W43 : bv 32 := 0x00a59533.
Lemma D43 : decode_any W43 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2BTg0028j1ATg002Zj18Tg003Kj11Tg0040j14Tg004Uj1:Tg0053j10Tg005Qj32Tg00E@j47Tg006`j46Tg007@j25Tg007bj33j19Tg008<j4@Tg008Zj2?Tg0097j6;Tg009Oj2<Tg009ij2=Tg00:Gj3>Tg00:oR0g00;[R1'BR2#AR3g00mG#8R4P0P1g00Mgg00=Y#1R5#4R6#:R7%16#0g00>>R832R9%46#0=278P9C7%15#0C6,52R533R9P3P3%93P0g00>ZP1g00?KC@,?2P4P5E;R5g00?dR4g00@DR2'<1=95=342d3>o"). Qed.
Lemma E43 : is_ecall W43 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
(* [comment removed for export] *)
Definition W44 : bv 32 := 0xfff54513.
Lemma D44 : decode_any W44 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2p;1p;3p;4p;6g001Xj2CTg0028j1BTg002Zj1:Tg003Kj11Tg0040j12Tg004Uj16Tg0053j13Tg005Qj34Tg00[Zj49Tg006`j47Tg007@j28Tg007bj35j1ATg008<j4@Tg008Zj2?Tg0097j6<Tg009Oj2=Tg009ij2>Tg00:Gj3;Tf0#2#2p=0g00:oR0g00;[R1'CR2#BR3g00n<#:R4P0P1g00];g00=YR5#1R6#2R7#6%17#3g00>>R734R8P8%25R5#1#1#6%05#0#0#0#0#3;47C9%16#3C7,82R635R7P3P3%A3P0g00>ZP1g00?KC@,?2P4P6E<R6g00?dR4g00@DR2'=1>76=542d3;o"). Qed.
Lemma E44 : is_ecall W44 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMaxVA ()) [] "p;2g009Oj20Tg00?dg00@d'0o"). Qed.
Definition MAXVA_WORDS : list (bv 32) := [W0; W1; W2; W3; W4; W5; W6; W7; W8; W9; W10; W11; W12; W13; W14; W15; W16; W17; W18; W19; W20; W21; W22; W23; W24; W25; W26; W27; W28; W29; W30; W31; W32; W33; W34; W35; W36; W37; W38; W39; W40; W41; W42; W43; W44].

(* [comment removed for export] *)
Lemma step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_and_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_and (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_and segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_sll_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLL rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_sll (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_sll segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_subw_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_subw (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.

(* [comment removed for export] *)
Definition topfull (k : Z) (v : Z) : Prop :=
  0 <= v /\ (forall i, 47 - k <= i <= 46 -> Z.testbit v i = true) /\ (forall i, 47 <= i -> Z.testbit v i = false).

Lemma topfull_init : forall x, 2 ^ 46 <= x < 2 ^ 47 -> topfull 1 x.
Proof.
  intros x Hx. split; [lia|]. split.
  - intros i Hi. assert (i = 46) by lia. subst i. apply Z.testbit_true; [lia|].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    replace (x / 2 ^ 46) with 1 by nia. reflexivity.
  - intros i Hi. apply Z.testbit_false; [lia|].
    assert (Hp : 2 ^ 47 <= 2 ^ i) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.div_small by lia. reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma topfull_step : forall k j v, 1 <= j <= k -> topfull k v -> topfull (Z.min (k + j) 47) (Z.lor v (Z.shiftr v j)).
Proof.
  intros k j v Hj (H0 & H1 & H2). split; [|split].
  - apply Z.lor_nonneg. split; [exact H0 | apply Z.shiftr_nonneg; exact H0].
  - intros i Hi. rewrite Z.lor_spec. destruct (Z_le_dec (47 - k) i) as [Hle|Hgt].
    + rewrite (H1 i) by lia. reflexivity.
    + rewrite Z.shiftr_spec by lia. rewrite (H1 (i + j)) by lia. apply orb_true_r.
  - intros i Hi. rewrite Z.lor_spec, Z.shiftr_spec by lia. rewrite (H2 i), (H2 (i + j)) by lia. reflexivity.
Qed.

Lemma topfull_all : forall v, topfull 47 v -> v = 2 ^ 47 - 1.
Proof.
  intros v (H0 & H1 & H2). apply Z.bits_inj'. intros i Hi.
  change (2 ^ 47 - 1) with (Z.ones 47).
  destruct (Z_lt_dec i 47) as [Hlt|Hge].
  - rewrite Z.ones_spec_low by lia. apply H1. lia.
  - rewrite Z.ones_spec_high by lia. apply H2. lia.
Qed.

(* [comment removed for export] *)
Lemma u_orsrl : forall (a : word) (j : Z), 0 <= j ->
  bv_unsigned (v_or a (v_srli a j)) = Z.lor (bv_unsigned a) (Z.shiftr (bv_unsigned a) j).
Proof.
  intros a j Hj. pose proof (u64_range a) as Ra.
  assert (Hs : 0 <= Z.shiftr (bv_unsigned a) j < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj) as Hp.
    split; [apply Z.div_pos; lia|]. apply Z.le_lt_trans with (bv_unsigned a); [|lia].
    apply Z.div_le_upper_bound; [lia|]. nia. }
  unfold v_or, v_srli. rewrite (u64_lit (Z.shiftr (bv_unsigned a) j)) by lia.
  apply u64_lit. apply Z_lor_range; lia.
Qed.


Lemma smear47 : forall x : word, 2 ^ 46 <= bv_unsigned x < 2 ^ 47 ->
  (v_or (v_or (v_or (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) (v_srli (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) 8)) (v_srli (v_or (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) (v_srli (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) 8)) 16)) (v_srli (v_or (v_or (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) (v_srli (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) 8)) (v_srli (v_or (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) (v_srli (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) 8)) 16)) 32)) = Z_to_bv 64 0x7fffffffffff.
Proof.
  intros x Hx.
  set (s1 := v_or x (v_srli x 1)). set (s2 := v_or s1 (v_srli s1 2)). set (s3 := v_or s2 (v_srli s2 4)).
  set (s4 := v_or s3 (v_srli s3 8)). set (s5 := v_or s4 (v_srli s4 16)).
  pose proof (topfull_init _ Hx) as T0.
  pose proof (topfull_step 1 1 _ ltac:(lia) T0) as T1. rewrite <- (u_orsrl x 1) in T1 by lia. fold s1 in T1. change (Z.min (1 + 1) 47) with 2 in T1.
  pose proof (topfull_step 2 2 _ ltac:(lia) T1) as T2. rewrite <- (u_orsrl s1 2) in T2 by lia. fold s2 in T2. change (Z.min (2 + 2) 47) with 4 in T2.
  pose proof (topfull_step 4 4 _ ltac:(lia) T2) as T3. rewrite <- (u_orsrl s2 4) in T3 by lia. fold s3 in T3. change (Z.min (4 + 4) 47) with 8 in T3.
  pose proof (topfull_step 8 8 _ ltac:(lia) T3) as T4. rewrite <- (u_orsrl s3 8) in T4 by lia. fold s4 in T4. change (Z.min (8 + 8) 47) with 16 in T4.
  pose proof (topfull_step 16 16 _ ltac:(lia) T4) as T5. rewrite <- (u_orsrl s4 16) in T5 by lia. fold s5 in T5. change (Z.min (16 + 16) 47) with 32 in T5.
  pose proof (topfull_step 32 32 _ ltac:(lia) T5) as T6. rewrite <- (u_orsrl s5 32) in T6 by lia. change (Z.min (32 + 32) 47) with 47 in T6.
  apply topfull_all in T6. apply bv_eq. rewrite T6. reflexivity.
Qed.

(* [comment removed for export] *)
Local Ltac greg := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ]; rewrite ?getr_zero.
Local Ltac wlit := greg; first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].

Section Block.
  Variable SEGS : list Segment.
  Variable x : Z.
  Hypothesis Hx : 0 <= x /\ x + 180 < 2 ^ 64.
  Hypothesis CODE : forall i, (i < 45)%nat -> fetch_word SEGS (Z_to_bv 64 (x + 4 * Z.of_nat i)) = Some (nth i MAXVA_WORDS W0).

  Definition maxva_post (regs regs' : bvmap 5 word) : Prop :=

    getr regs' 10 = Z_to_bv 64 0x7fffffffffff /\ getr regs' 11 = Z_to_bv 64 0xffffffffffffffff /\ getr regs' 12 = Z_to_bv 64 0x3333333333333333 /\ getr regs' 13 = Z_to_bv 64 0xf0f0f0f0f0f0f0f /\ getr regs' 14 = Z_to_bv 64 0x101010101010101 /\ getr regs' 15 = Z_to_bv 64 0x7fffc00000000000
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).

  Lemma maxva_block : forall regs M rom,
    2 ^ 46 <= bv_unsigned (getr regs 10) < 2 ^ 47 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' (Z_to_bv 64 (x + 180)) M rom)
      /\ maxva_post regs regs'.
  Proof.
    intros regs M rom Hx10.
    assert (C0 : fetch_word SEGS (Z_to_bv 64 x) = Some W0).
    { replace x with (x + 4 * Z.of_nat 0) at 1 by lia. exact (CODE 0%nat ltac:(lia)). }
    eexists. split.
    -
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W0 11 10 (1 : bv 6) (v_srli (getr regs 10%bv) 1) C0 E0 D0 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 1).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_lui_at SEGS _ _ M rom W1 12 (349525 : bv 20) (Z_to_bv 64 0x55555000) (CODE 1%nat ltac:(lia)) E1 D1 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 2).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_lui_at SEGS _ _ M rom W2 13 (209715 : bv 20) (Z_to_bv 64 0x33333000) (CODE 2%nat ltac:(lia)) E2 D2 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 3).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_lui_at SEGS _ _ M rom W3 14 (61681 : bv 20) (Z_to_bv 64 0xf0f1000) (CODE 3%nat ltac:(lia)) E3 D3 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 4).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_lui_at SEGS _ _ M rom W4 15 (4112 : bv 20) (Z_to_bv 64 0x1010000) (CODE 4%nat ltac:(lia)) E4 D4 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 5).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_or_at SEGS _ _ M rom W5 10 10 11 (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (CODE 5%nat ltac:(lia)) E5 D5 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 6).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_addiw_at SEGS _ _ M rom W6 11 12 (1365 : bv 12) (Z_to_bv 64 0x55555555) (CODE 6%nat ltac:(lia)) E6 D6 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 7).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_addiw_at SEGS _ _ M rom W7 12 13 (819 : bv 12) (Z_to_bv 64 0x33333333) (CODE 7%nat ltac:(lia)) E7 D7 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 8).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_addiw_at SEGS _ _ M rom W8 13 14 (3855 : bv 12) (Z_to_bv 64 0xf0f0f0f) (CODE 8%nat ltac:(lia)) E8 D8 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 9).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_addiw_at SEGS _ _ M rom W9 14 15 (257 : bv 12) (Z_to_bv 64 0x1010101) (CODE 9%nat ltac:(lia)) E9 D9 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 10).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W10 15 10 (2 : bv 6) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2) (CODE 10%nat ltac:(lia)) E10 D10 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 11).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_or_at SEGS _ _ M rom W11 10 10 15 (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (CODE 11%nat ltac:(lia)) E11 D11 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 12).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_slli_at SEGS _ _ M rom W12 15 11 (32 : bv 6) (Z_to_bv 64 0x5555555500000000) (CODE 12%nat ltac:(lia)) E12 D12 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 13).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_add_at SEGS _ _ M rom W13 11 11 15 (Z_to_bv 64 0x5555555555555555) (CODE 13%nat ltac:(lia)) E13 D13 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 14).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_slli_at SEGS _ _ M rom W14 15 12 (32 : bv 6) (Z_to_bv 64 0x3333333300000000) (CODE 14%nat ltac:(lia)) E14 D14 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 15).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_add_at SEGS _ _ M rom W15 12 12 15 (Z_to_bv 64 0x3333333333333333) (CODE 15%nat ltac:(lia)) E15 D15 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 16).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_slli_at SEGS _ _ M rom W16 15 13 (32 : bv 6) (Z_to_bv 64 0xf0f0f0f00000000) (CODE 16%nat ltac:(lia)) E16 D16 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 17).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_add_at SEGS _ _ M rom W17 13 13 15 (Z_to_bv 64 0xf0f0f0f0f0f0f0f) (CODE 17%nat ltac:(lia)) E17 D17 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 18).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_slli_at SEGS _ _ M rom W18 15 14 (32 : bv 6) (Z_to_bv 64 0x101010100000000) (CODE 18%nat ltac:(lia)) E18 D18 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 19).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_add_at SEGS _ _ M rom W19 14 14 15 (Z_to_bv 64 0x101010101010101) (CODE 19%nat ltac:(lia)) E19 D19 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 20).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W20 15 10 (4 : bv 6) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4) (CODE 20%nat ltac:(lia)) E20 D20 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 21).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_or_at SEGS _ _ M rom W21 10 10 15 (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (CODE 21%nat ltac:(lia)) E21 D21 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 22).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W22 15 10 (8 : bv 6) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8) (CODE 22%nat ltac:(lia)) E22 D22 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 23).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_or_at SEGS _ _ M rom W23 10 10 15 (v_or (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8)) (CODE 23%nat ltac:(lia)) E23 D23 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 24).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W24 15 10 (16 : bv 6) (v_srli (v_or (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8)) 16) (CODE 24%nat ltac:(lia)) E24 D24 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 25).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_or_at SEGS _ _ M rom W25 10 10 15 (v_or (v_or (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8)) (v_srli (v_or (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8)) 16)) (CODE 25%nat ltac:(lia)) E25 D25 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 26).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W26 15 10 (32 : bv 6) (v_srli (v_or (v_or (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8)) (v_srli (v_or (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8)) 16)) 32) (CODE 26%nat ltac:(lia)) E26 D26 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 27).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_or_at SEGS _ _ M rom W27 10 10 15 (Z_to_bv 64 0x7fffffffffff) (CODE 27%nat ltac:(lia)) E27 D27 eq_refl); greg; exact (smear47 _ Hx10) |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 28).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_xori_at SEGS _ _ M rom W28 10 10 (4095 : bv 12) (Z_to_bv 64 0xffff800000000000) (CODE 28%nat ltac:(lia)) E28 D28 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 29).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W29 15 10 (1 : bv 6) (Z_to_bv 64 0x7fffc00000000000) (CODE 29%nat ltac:(lia)) E29 D29 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 30).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_and_at SEGS _ _ M rom W30 11 15 11 (Z_to_bv 64 0x5555400000000000) (CODE 30%nat ltac:(lia)) E30 D30 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 31).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_sub_at SEGS _ _ M rom W31 10 10 11 (Z_to_bv 64 0xaaaa400000000000) (CODE 31%nat ltac:(lia)) E31 D31 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 32).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_and_at SEGS _ _ M rom W32 11 10 12 (Z_to_bv 64 0x2222000000000000) (CODE 32%nat ltac:(lia)) E32 D32 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 33).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W33 10 10 (2 : bv 6) (Z_to_bv 64 0x2aaa900000000000) (CODE 33%nat ltac:(lia)) E33 D33 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 34).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_and_at SEGS _ _ M rom W34 10 10 12 (Z_to_bv 64 0x2222100000000000) (CODE 34%nat ltac:(lia)) E34 D34 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 35).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_add_at SEGS _ _ M rom W35 10 11 10 (Z_to_bv 64 0x4444100000000000) (CODE 35%nat ltac:(lia)) E35 D35 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 36).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W36 11 10 (4 : bv 6) (Z_to_bv 64 0x444410000000000) (CODE 36%nat ltac:(lia)) E36 D36 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 37).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_add_at SEGS _ _ M rom W37 10 10 11 (Z_to_bv 64 0x4888510000000000) (CODE 37%nat ltac:(lia)) E37 D37 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 38).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_and_at SEGS _ _ M rom W38 10 10 13 (Z_to_bv 64 0x808010000000000) (CODE 38%nat ltac:(lia)) E38 D38 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 39).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_mul_at SEGS _ _ M rom W39 10 10 14 (Z_to_bv 64 0x1109010000000000) (CODE 39%nat ltac:(lia)) E39 D39 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 40).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W40 10 10 (56 : bv 6) (Z_to_bv 64 0x11) (CODE 40%nat ltac:(lia)) E40 D40 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 41).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_subw_at SEGS _ _ M rom W41 10 0 10 (Z_to_bv 64 0xffffffffffffffef) (CODE 41%nat ltac:(lia)) E41 D41 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 42).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_addi_at SEGS _ _ M rom W42 11 0 (4095 : bv 12) (Z_to_bv 64 0xffffffffffffffff) (CODE 42%nat ltac:(lia)) E42 D42 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 43).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_sll_at SEGS _ _ M rom W43 10 11 10 (Z_to_bv 64 0xffff800000000000) (CODE 43%nat ltac:(lia)) E43 D43 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 44).
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | eapply (step_xori_at SEGS _ _ M rom W44 10 10 (4095 : bv 12) (Z_to_bv 64 0x7fffffffffff) (CODE 44%nat ltac:(lia)) E44 D44 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 45).
      pc_is (x + 180). apply mst_refl.
    - unfold maxva_post. repeat split; try (greg; reflexivity).   (* [comment removed for export] *)
      intros r N10 N11 N12 N13 N14 N15. repeat (rewrite getr_other by assumption). reflexivity.
  Qed.
End Block.
