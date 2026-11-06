(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS02 Require Import AsanMemcpyBase AsanMemcpyAL Asan_code_memcpy.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import PropExec.
Ltac2 kr_t_AsanMemcpyMIS () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib2K52AS5Hoare3at_C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K54AS02>AsanMemcpyBase4memkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K52AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula05C69OSSVerify5KrLib2K54AS02>AsanMemcpyBase6mc_lbuC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC69OSSVerify5KrLib2K52AS8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib2K54AS02>AsanMemcpyBase2b_C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib2K52AS8PropExec9step_addiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02>AsanMemcpyBase<sb_val_plainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02>AsanMemcpyBase5mc_sbC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpK69OSSVerify5KrLib2K52AS6CatSim6msteps01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib2K52AS8PropExec8v_addi_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS5Hoare7at_addiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<RefMemcpyLib:keeps_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib2K52AS<RefMemcpyLib:not_kept_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<RefMemcpyLib9keeps_updC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K52AS8PropExec4mkstC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<RefMemcpyLib3LBvC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K69OSSVerify5KrLib2K52AS6CatSim6msteps02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbK47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01c69OSSVerify5KrLib2K54AS02=AsanMemcpyMIS>asanreflect_fxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgITgt_bilateral_fuzzer_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02>AsanMemcpyBase>asanreflect_fxC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C69OSSVerify5KrLib2K52AS<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed9cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed9cC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed9cC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1N00C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_beda0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_beda0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_beda0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums8positive00C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_beda4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_beda4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_beda4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_beda8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_beda8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_beda8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bedacC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bedacC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bedacC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bedb0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bedb0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bedb0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bedb4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bedb4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bedb4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bedb8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bedb8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bedb8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bedbcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bedbcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bedbcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bedc0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bedc0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bedc0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bedc4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bedc4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bedc4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed48C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed48C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed48C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed4cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed4cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed4cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed50C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed50C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed50C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed54C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed54C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed54C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed58C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed58C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed58C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed5cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed5cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed5cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed60C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed60C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed60C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed68C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed68C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed68C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed6cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed6cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed6cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed70C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed70C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed70C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed74C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed74C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed74C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed78C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed78C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed78C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed7cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed7cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed7cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed80C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed80C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed80C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed84C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed84C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed84C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed88C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed88C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed88C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed8cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed8cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed8cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed90C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed90C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed90C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becb4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becb4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becb4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becb8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becb8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becb8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becbcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becbcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becbcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becc0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becc0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becc0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becc4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becc4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becc4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becc8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becc8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becc8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becccC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becccC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becccC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becd0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becd0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becd0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becd4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becd4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becd4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becd8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becd8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becd8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becdcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becdcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becdcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bece0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bece0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bece0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bece4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bece4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bece4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bece8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bece8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bece8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bececC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bececC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bececC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becf0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becf0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becf0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becf4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becf4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becf4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becf8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becf8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becf8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_becfcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_becfcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_becfcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed0cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed0cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed0cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed18C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed18C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed18C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed1cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed1cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed1cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed20C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed20C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed20C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed24C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed24C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed24C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed28C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed28C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed28C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed2cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed2cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed2cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed30C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed30C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed30C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed34C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed34C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed34C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed38C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed38C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed38C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed3cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed3cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed3cC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K52AS8PropExec6v_andiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec4c_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib2K52AS7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib2K54AS02>AsanMemcpyBase6u_andiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec;step_bne_ftC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec4btgtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec;step_jal_x0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K52AS8PropExec;step_bne_tkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54AS02=AsanMemcpyMIS6b4_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<RefMemcpyLib;keeps_transC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC69OSSVerify5KrLib2K52AS<RefMemcpyLib:runs_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec9step_andiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bea70C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bea70C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bea70C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bea74C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bea74C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bea74C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bea78C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bea78C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bea78C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec;step_beq_tkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed94C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed94C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed94C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed98C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed98C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed98C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegc69OSSVerify5KrLib2K54AS02=AsanMemcpyMIS6t4_runC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rc69OSSVerify5KrLib2K54AS02=AsanMemcpyMIS6b8_blkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54AS02=AsanMemcpyMIS7b8_tailC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bea68C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bea68C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bea68C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bea6cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bea6cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bea6cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed40C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed40C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed40C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bed44C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bed44C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bed44C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02>AsanMemcpyBase9bits_lt32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC69OSSVerify5KrLib2K52AS8PropExec<step_bgeu_ftC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54AS02=AsanMemcpyMIS6t8_runC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC69OSSVerify5KrLib2K52AS8PropExec<step_bgeu_tkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54AS02=AsanMemcpyMIS7b16_blkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54AS02=AsanMemcpyMIS8b16_tailC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bea60C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bea60C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bea60C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7W_bea64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7F_bea64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02@Asan_code_memcpy7D_bea64C1?~~~~~~~~~~~~~~~".  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MIS.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac sbp := apply sb_val_plain.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b4_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0xf41dc : word) (MK k) rom) (mkst regs' (0xf4208 : word) (MK (k + 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
    - mlbu F_bed9c D_bed9c k. mlbu F_beda0 D_beda0 (k+1)%Z. mlbu F_beda4 D_beda4 (k+2)%Z. mlbu F_beda8 D_beda8 (k+3)%Z.
      stepn F_bedac D_bedac.                            
      stepn F_bedb0 D_bedb0.                            
      msb F_bedb4 D_bedb4 k ltac:(sbp). msb F_bedb8 D_bedb8 (k+1)%Z ltac:(sbp).
      msb F_bedbc D_bedbc (k+2)%Z ltac:(sbp). msb F_bedc0 D_bedc0 (k+3)%Z ltac:(sbp).
      stepn F_bedc4 D_bedc4.                            
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0xf4188 : word) (MK k) rom) (mkst regs' (0xf41d4 : word) (MK (k + 8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
    - mlbu F_bed48 D_bed48 k. mlbu F_bed4c D_bed4c (k+1)%Z. mlbu F_bed50 D_bed50 (k+2)%Z. mlbu F_bed54 D_bed54 (k+3)%Z.
      mlbu F_bed58 D_bed58 (k+4)%Z. mlbu F_bed5c D_bed5c (k+5)%Z. mlbu F_bed60 D_bed60 (k+6)%Z. mlbu F_bed64 D_bed64 (k+7)%Z.
      stepn F_bed68 D_bed68.                            
      msb F_bed6c D_bed6c k ltac:(sbp). msb F_bed70 D_bed70 (k+1)%Z ltac:(sbp).
      msb F_bed74 D_bed74 (k+2)%Z ltac:(sbp). msb F_bed78 D_bed78 (k+3)%Z ltac:(sbp).
      stepn F_bed7c D_bed7c.                            
      msb F_bed80 D_bed80 (k+4)%Z ltac:(sbp). msb F_bed84 D_bed84 (k+5)%Z ltac:(sbp).
      msb F_bed88 D_bed88 (k+6)%Z ltac:(sbp). msb F_bed8c D_bed8c (k+7)%Z ltac:(sbp).
      stepn F_bed90 D_bed90.                            
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0xf40f4 : word) (MK k) rom) (mkst regs' (0xf4180 : word) (MK (k + 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
    - mlbu F_becb4 D_becb4 k. mlbu F_becb8 D_becb8 (k+1)%Z. mlbu F_becbc D_becbc (k+2)%Z. mlbu F_becc0 D_becc0 (k+3)%Z.
      mlbu F_becc4 D_becc4 (k+4)%Z. mlbu F_becc8 D_becc8 (k+5)%Z. mlbu F_beccc D_beccc (k+6)%Z. mlbu F_becd0 D_becd0 (k+7)%Z.
      msb F_becd4 D_becd4 k ltac:(sbp). msb F_becd8 D_becd8 (k+1)%Z ltac:(sbp).
      msb F_becdc D_becdc (k+2)%Z ltac:(sbp). msb F_bece0 D_bece0 (k+3)%Z ltac:(sbp).
      mlbu F_bece4 D_bece4 (k+8)%Z. mlbu F_bece8 D_bece8 (k+9)%Z. mlbu F_becec D_becec (k+10)%Z. mlbu F_becf0 D_becf0 (k+11)%Z.
      msb F_becf4 D_becf4 (k+4)%Z ltac:(sbp). msb F_becf8 D_becf8 (k+5)%Z ltac:(sbp).
      msb F_becfc D_becfc (k+6)%Z ltac:(sbp). msb F_bed00 D_bed00 (k+7)%Z ltac:(sbp).
      mlbu F_bed04 D_bed04 (k+12)%Z. mlbu F_bed08 D_bed08 (k+13)%Z. mlbu F_bed0c D_bed0c (k+14)%Z. mlbu F_bed10 D_bed10 (k+15)%Z.
      stepn F_bed14 D_bed14.                            
      msb F_bed18 D_bed18 (k+8)%Z ltac:(sbp). msb F_bed1c D_bed1c (k+9)%Z ltac:(sbp).
      msb F_bed20 D_bed20 (k+10)%Z ltac:(sbp). msb F_bed24 D_bed24 (k+11)%Z ltac:(sbp).
      stepn F_bed28 D_bed28.                            
      msb F_bed2c D_bed2c (k+12)%Z ltac:(sbp). msb F_bed30 D_bed30 (k+13)%Z ltac:(sbp).
      msb F_bed34 D_bed34 (k+14)%Z ltac:(sbp). msb F_bed38 D_bed38 (k+15)%Z ltac:(sbp).
      stepn F_bed3c D_bed3c.                            
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma t4_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0xf3eb0 : word) (MK k) rom) (mkst regs' (0xf4208 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_bea70 D_bea70.                          
        stepb_ft F_bea74 D_bea74 ltac:(cond).           
        stepn F_bea78 D_bea78.                          
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0xf41dc : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_bea70 D_bea70.
          stepb_tk F_bea74 D_bea74 ltac:(cond).         
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0xf41d4 : word) (MK k) rom) (mkst regs' (0xf4208 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_bed94 D_bed94.                          
        stepb_tk F_bed98 D_bed98 ltac:(cond).           
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0xf41dc : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_bed94 D_bed94.
          stepb_ft F_bed98 D_bed98 ltac:(cond).         
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t8_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0xf3ea8 : word) (MK k) rom)
                   (mkst regs' (0xf4208 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - 
      eapply (runs_trans ASEGS _ (fun r => mkst r (0xf3eb0 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_bea68 D_bea68.                        
          stepb_ft F_bea6c D_bea6c ltac:(cond).         
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - 
      eapply (runs_trans ASEGS _ (fun r => mkst r (0xf4188 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_bea68 D_bea68.
          stepb_tk F_bea6c D_bea6c ltac:(cond).         
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans ASEGS _ (fun r => mkst r (0xf41d4 : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
          split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0xf4180 : word) (MK k) rom)
                   (mkst regs' (0xf4208 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0xf3eb0 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_bed40 D_bed40.                        
          stepb_tk F_bed44 D_bed44 ltac:(cond).         
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0xf4188 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_bed40 D_bed40.
          stepb_ft F_bed44 D_bed44 ltac:(cond).         
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans ASEGS _ (fun r => mkst r (0xf41d4 : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t16_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 32)%Z -> (0 <= k)%Z ->
    (k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0xf3ea0 : word) (MK k) rom)
                   (mkst regs' (0xf4208 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
    destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - 
      eapply (runs_trans ASEGS _ (fun r => mkst r (0xf3ea8 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_bea60 D_bea60.                        
          stepb_ft F_bea64 D_bea64 ltac:(cond).         
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - 
      eapply (runs_trans ASEGS _ (fun r => mkst r (0xf40f4 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_bea60 D_bea60.
          stepb_tk F_bea64 D_bea64 ltac:(cond).         
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans ASEGS _ (fun r => mkst r (0xf4180 : word) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
