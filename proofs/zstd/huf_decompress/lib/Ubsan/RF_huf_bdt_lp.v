(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_bdt_lp () := "C46Stdlib5Lists4List8map_consC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6shiftlC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z4landK47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI45stdpp9bitvector;definitions2bv00C47Corelib4Init3Nat3mulC47Corelib4Init3Nat3addC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model@u16s_prefix_snocC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem9upd_bytesC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sC46Stdlib5Lists4List:length_mapC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List7map_appC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef3mapC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC45stdpp9bitvector;definitions7bv_wrapC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<Z_to_bv8_modC35stdpp7tactics<f_equal_helpC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallI47Corelib4Init5Logic4True00C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit:swrap32_eqI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp<lowprob_loopK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_bdt_lp5lp_okc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_bdt_lp6lp_invK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model4tsymC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model;tsym_lengthC46Stdlib5Lists4List<length_skipnC47Corelib4Init3Nat3subC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount8to_shortC56Stdlib6ZArith6BinInt1Z3lebC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model;bind_Ok_invI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model7load_OkC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem8u16_znthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx16K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr06I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude4zextC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le2C56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr05C47Corelib4Init9Datatypes4negbC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6ostoreC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sraiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_sraiC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_sltK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_sltC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8leb_specC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;u16s_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission6Common6StrFun@u8arr_store_ok_nC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07K4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_2'C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le2C5ARocqVerifyHarness?AgentSubmission6Common6StrFunAu8arr_write_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writec5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_bdt_lp:snext_snocK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3u16I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_donec5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_bdt_lp<land_neg_b2zC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_b2zC5ARocqVerifyHarness?AgentSubmission6Common<FseWalkArith:slt_lit_mrC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9v_slt_b2zc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_bdt_lp<srai48_shortC46Stdlib4Bool4Bool>negb_false_iffC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model9ostore_OkC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model:tsym_storeC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8oupd_natC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT?oupd_nat_lengthc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_bdt_lp;swrap32_u32C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_bdt_lp;shl32_shr30C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem:zx16_shortC47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_bdt_lp4lp_WC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z8inj_succI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK4ELinuxProcessSemantics5Riscv5Instr5msize02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5aluop02C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop0:C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I46Stdlib5Lists4List6Exists00K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5msize01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srai48_short : forall c, - 32768 <= c < 32768 -> bv_signed (Z_to_bv 64 ((c mod 65536) ≪ 48)) ≫ 48 = c.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_lp ()) [] "h01zh17__arithh24__ffh38__varmaph45__with54__x1h64__x2h74__x3h84__x4h94__x5h:4__x6h;4__x7h<1Hh=2H0h>2H1h?3H10h@3H11hA3H12hB3H13hC2H2hD2H3hE2H4hF2H5hG2H6hH2H7hI2H8hJ2H9hK2HchL1chM1qhN2q0hO2q1hP1rhQ2r0hR2r1p&0p;1p;2p;3p;4p;6p;7p;8p10000p4p7210g000MR0p4p710p8g000kj11Tg001Pj1PTg001nj2BTg002Jj1ATg002hj22Tg003Dj2:Tg003_j1pTg004=j20Tg004]j1STg005Bj2lTg005bj2aTg006Ij2^Tg006ij2}Tg007Fj2KTg007cj28Tg008@j2;Tg008]j2XTg009>j1_Tg009Wj2`Tg00:>j2WTg00:ej2VTg00;Kj2UTg00<1j16Tg00<Pj2dTg00=9j2QTg00=bj3JTg00>Kj2cTg00>lj3HTg00?Uj2bTg00@Aj2GTg00@mk104Tg00AMj3iTg00Amk103Tg00BMj2OTg00Bkj4]Tg00CIk102Tg00Cgk101Tg00DRj2hTg00E5j1|Tg00EWj3NTg00F:j3LTg00F]j3{Tg00G@j2gTg00Gcj2zTg00HEj2yTg00H_j2xTg00IKj3YTg00Iej3tTg00JDj4sTg00K6j1rTg00KTj3uTP0j6RTg00L=j3qTg00Lfj2vTg00MLj2wTg00N4j2oTg00Naj2fTg00O>j3\Tg00Ogj4TTg00PRj7nTg00Q6j6~Tg00QZj8mTg00R>k700Tf0R0#1#1#1#1p=j%10#1#1#1#1#1#1#1p=E%10#1p=eg00RbR1f1R2;Y0p=4f2R3/f2/00p=<g00S@R49Y10p=D1032/K0p=@1K32/f0p=51B40p=F1d10p=9A\1209\13p=>A\120p=k1h10p=?P1P2g00S^P0CTp==P2g00TER5g00TdR6P6g00UDR7P0g00UdFnp=3P2P5P6P6P7P0E~p=[1g10p=Cf3R8P5P6P6P7P3P2P0Gmp=7P1P2g00VDP0CTp=IP1P2g00VkP0CTp=MP3P5P6P6P7P2P0K00p=Zg00WRR5#1R9#1R:#jR;#1#ER<#PR=/B0%A<R>,20':P1%p;R;%1<R<#AR?,02R@%S5RA#1RB#1#e#ARC'lRD'a1^0C/43X01P1%A9/}CRE,K@RF1a;0/^C/43X01P11a;FRF/8ERE1403X01%E<#E#E#ER<#ARG,K@%1<#e#j#ERH#ARI%1H#ARH3</;I/XG%DGRJ#_A@3?G?<IH/;IRK18KG10KG55G'4[1`KG124GRKA@8?G?<IH/;IRL/0GRM#F12MG':[1WLG12G4f4RL?@?G?<IH/;IRM/0GRN,2G1BN4':[1VMGf5RM?@?G?<IH/;IRN/8G#D\J1UNGf6RN?@?G?<IH/;IRO/0G/4O\J18OGP1f7RO?@?G?<IH/;I/0GP1f8RP/0??5GI/XH%DHRQ#_f9RR/0??5GIRS18SH10SH55H'4[1`SH124HRSf:/0??5GIRT/0HRU#F12UH':[1WTH12H4f;/0??5GIRT/0HRU,2H1BU4':[1VTHf</0??5GIRT/8H#D\Q1UTHf=RT/0??5GIRU/0H/4U\Q18UHP1f>RU?@?G?<IHP1f?RV/X?%D?RW#_f@RX18X?10X?55?'4[1`X?124?fARY/0?RZ#F12Z?':[1WY?12?4fBRY/0?RZ,2?1BZ4':[1VY?fCRY/8?#D\W1UY?fDRY/0?/4Y\W18Y?P1fERZ/0?P1g00X7R[g00XcR\#6R]#6#6R^#6R_#6R`#6Ra#9Rb%9_R_%9^R^3>1d1\R\%6a#6Ra#6Rc#6Rd#9%9]R]3>1Q1H=J1\%P<,c1R<%6dRd#6#9Re5H1%9d%P5,c1Rd%9cRc5H11Q1GRf=J1_3>3>g00YBR_'b,G\'G'GAH1<cAH1db%9`R`AH1d^AJ1f\3>3>%9a,kc1Q1?=J1]1ke`5>\/b_'G,G\'G&04[R\5i[3i&03[R[P1P11O1LP31O1NC]P2P11O1MP81O1OC]C]&021R8&011R_P_%??R`1h14Re'=,3_,[_%|6R6%C9R]%SA#C9N1`%S9#CR95L1'=,3_C7P6P_P_%?HR`,Ie,3_P6%CARA,Me,3_1IA`,3_5Z_C7P6P_P_1=`e,3_,[_P6%?GRc9N19%?IR95L1%CB9N1`=L1A'=,3_C7P6P_P_1Iec,3_P6%C:R:,Me,3_1I:c,3_5Z_C7P6P_P_1=ce,3_,[_P6A{1A91g15R59N1c=L1:'=,3_C7P6P_%?=/M],3_%?>,I],3_5Z_P61=5],3_C7C7C7C7C7C71z_7R7P0P3g00YnR5g00ZNR]'y1x03=Y5]dAt142CsR4b2b3b4X51X61X71X81X91X:1X;1g00ZnR]\WA5?OM,43[%FL12LH':\SP]\QA5OGIA5HPM'4[%FO12OG':\KP]\J1;OIA5GMP'4[1B=N12N>':14NO[[[[[[^51^61^71^81^91^:1^;1P0P3PRP2PVPPfGPXPOPTPUPYPZfFO=b1bRbObBbAb@b?bJbQbNbIbHbGbFbEbPbMbDbCb>b=b<14E2e1^FCP\P[%r1P8%?C,Me,3_P7P4b2b3b4%FCP0b1R09uFCERPDAq@C0ER1v;D,w;1o;DERWKXL1o"). Qed.

(* [comment removed for export] *)
Lemma land_neg_b2z : forall (b : bool) fm, fm = 0 \/ fm = 1 ->
  Z.land ((0 - Z.b2z b) mod 18446744073709551616) fm = (if b then fm else 0).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_lp ()) [] "p'0h01Hh12fmh21bi001bp;1p;2p;6p;3g002Jj1;Tg00[KR0j2<Tg00[ej18Tg008@j27Tg004=j26Tg00\Bj24Tg00HEj2:Tg000Mj65Tg00IKj39Tg000kj10Tg00RbR1f0R2g00S@R339p=3f1R4=912p=2%02#0#0#0#0#0#0#0p=1g00YnR5P5%32g00WRR6#;R7,22'<R8f2R9#8,73%16#1#1#1#1#1#1#1#;R6'6/44P5P1P9P4P3n0110000020000'2[^11P2P0%34R51247R4g00ZN#8,73/66R:/49/29P2%39R;P1P314:2/22X11R:1:13R<f3R=P2E5W0P2O11297R>P1P7P:1:17P=P2E5W0P2O1n200100000021000010000X08X11P0P5P4g00\`#8,73/66R6/49#3P2P1P31462#3X11R6P<P=P2E5X0;P2O1P1P7P6P<P=P2E5X0>P2O1n200100000021000010000X08X11n0110000020101W2o"). Qed.

(* [comment removed for export] *)
Lemma snext_snoc : forall (snext : list Z) (jw : list byte) (v : Z), (2 * length snext + 2 <= length jw)%nat ->
  upd_bytes (u16s (map (Z_to_bv 64) snext) ++ skipn (2 * length snext) jw) (2 * length snext) (le2 (Z_to_bv 64 v))
  = u16s (map (Z_to_bv 64) (snext ++ [v])) ++ skipn (2 * length (snext ++ [v])) jw.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_lp ()) [] "h01nh11Eh24__x1h34__x2h41lh51Hh62H0h77__arithh84__ffh98__varmaph:5__with;4cstrh<5cstr0h=2jwh>5snexth?1vp;1p;2p;3p;4p;6p;5p;7p;8p;Bp;<p100]@p4p7210g000MR0p4p710p8g00Amj1BTg000kj18Tg003_j1MTg00]lj1JTg00<1j1PTg00^Oj21Tg00^fj23Tg00_=j20Tg00_]R1j2;Tg00Lfj1Wj2CTg00`7j3mTg00aCj39Tg00aaj1HTg00bQj3ITg00@mj1GTg00AMj3>Tg00cGj32Tg00IKj34Tg00cdj1FTg00d_j4LTg00e>j6YTg00HEj2=TP0j6<Tg00eZj3KTg00f9j5XTg002Jj1VTg00fUR0j1:Tg007FR2j2ETg00NaR3j2DTg001nR4j2?Tg00g5j4TTg00g\j1QTg00BMj2lTg00K6j1kTg00Bkj4jTg00CIj1iTg00Cgj1hTg00DRj2gTg00G@j2NTg00EWj3fTg00F:j3aTg00Ogj4`Tg00PRj7_Tg00E5j1^Tg00QZj8bTg00Gcj2cTg00H_j2]Tg00Iej3dTg00JDj4eTg00hAj4\Tg00hlj4[Tg00iHlBOTg00inl<ZTg00RbR5f0R6'0p=5P5f2R7f1R8P6C[p=6%F8=276p=7f3R91178;96p=Af4R:A9786729p=@g00jSR;P;P;P5P5P5g00k2P0P0P0P2g00kRf5R2P:P9P7P8P6MBOp=UP;P;P;P5P5P5g00l5P0P0P0P3g00lUP2P:P9P7P8P6MBOp=RP;P5P1P0P4g00m8P2P:P9P7P8P6M<Zp=S%B5g00WRR4#8R0#8#8R1#M#JR3#BR<g00Xc#P#PR=%57'1/3=1038';%81#8#8#MR1#JR>%W1R?;69R@1C187m710>@,1=/3=1037';A6>?:R@10>@RA,1=RB=9395731C17RC#H7IB%G>RB9>>C92>@R@P3P=10>@P9CA57354<[P;PA11=6RA/3=103:R@';f6RC96>?RD11=8RE=9325731C1:RF#H7IEP3A>>FBRF92>DRE#FRGP310>E,1=P2D@RE54<[X0;P6%5:RHP5P>P?P:CLEY11=H/3=1039';A6>?2RH%52RI,1=RJ=93:5731C19R1#H7IJRKA>>1BR192>HRBP3P=10>BRBP:CA573RL54<[P<PL%G5RL9>5:RM925CRN96>?P3P=%5NP2CARN57394<6X4<%B>ROA>59LRL96>?92>HRPA736N94<EX4OP;10>HRO10>1'3A93A2RA923GA6>?M92>D#FRE=23N54<X0;P;%5L,3IRNP3PGP310>D10>FRF'3,1=P2D@A23EA54<X0;P;PIP3PGP3136F,1=P2D@P3PEP3%5CRE%5M'3,1=P2D@54<X0;P3P=PNP:CA973P,=<POP5P>P?P2CLE<A252LRO#5AK52LE<PBAK>H1E<A6>?OP5P>P?P2PLDXE<PKP613J=RK/;@RL%V0R2%:IR?'ER>/D2RO%:@R1'?RHPKPOPJP>P=P21=52R>PIP?1=5?EUP=P2P>ERP@P11=51ESR1PLPHP1P7CTPH%QEg00S@RH%:E'?103CRC#Q%:C,?Hg00X7RC#G%BCP51l57P8%k5Cj%i5%h5RCg00TEREg00TdR1P1g00UDRLPCPEP1P1PLP51g52RE1N545f5=a5Eg00Vk1N50C`g00UdF_R0%^1P0Gb1cCLP6P7g00YnRLg00ZNRC'=1]67=4LCdAd5H8Ceb8b9b:X25X351E26/D2/?81E28/D2/?7[^25^35P6f8,03#:f9#5#:P9O3b7b<b;b6C\O1E<b1b1W5X?5W=W>o"). Qed.

Lemma le2_mod16 : forall x, le2 (Z_to_bv 64 x) = le2 (Z_to_bv 64 (x mod 65536)).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_lp ()) [] "h04__x1h15__x10h25__x11h34__x2h44__x3h54__x4h64__x5h74__x6h84__x7h94__x8h:4__x9h;1zh<7__arithh=4__ffh>8__varmaph?5__with@1HhA2H0hB2H1hC3H10hD3H11hE3H12hF3H13hG3H14hH3H15hI3H16hJ3H17hK3H18hL3H19hM2H2hN3H20hO3H21hP3H22hQ3H23hR2H3hS2H4hT2H5hU2H6hV2H7hW2H8hX2H9hY5__x12hZ5__x13h[5__x14h\5__x15h]1qh^2q0h_2q1h`2q2ha2q3hb1rhc2r0hd2r1he2r2hf2r3hg3H24hh3H25hi3H26hj3H27hk3H28hl3H29hm3H30hn3H31ho3H32hp3H33hq2q4hr2q5hs2r4ht2r5hu1xp%0p&0p;1p;2p;3p;4p;8p;6p;7g000kj14Tg003_j1|Tg00mZj2nTg00]lk10ETg00Amk100Tg00<1j12Tg00n@j2PTg002Jj1UTg004=j20Tg00Lfj2NTg00o=j2gTg00IKj39Tg00AMj2fj3Mk10ATg006Ij2qTg00@mk101Tg00HEj2mTg008]j2FTg009>j1kTg009Wj2ETg002hj2LTg00:>j2GTg00:ej2ITg00;Kj2HTg007cj26Tg001Pk104Tg00>Kk203Tg00<Pj2sTg00=9k202Tg00=bj3rTg00?Uj2eTg00K6k10DTg00CIk10CTg00Cgk10BTg00DRj2\Tg00E5k10@Tg004]j1RTg00G@j2}Tg00Gck20?Tg00H_k20>Tg00Iek30=Tg00JDk40<Tg007Fj2BTg00ogj3{Tg010`j8_Tg006ik20;Tg00@Aj2ZTg00KTj3yTg000Mj6]Tg011=j2xTg00aaj1wTg00Naj2vTg001nj2hTg003Dj2zTg00>lj3uTg00O>j3YTg00BMk208Tg00Bkk407Tg00Ogj4^Tg00PRj7iTg00Q6k606Tg00EWj3tTg00F:j3oTg00R>k705Tg00QZj8XTf0R0#4#4p>0F%40#4#4#4#4#4#4#4p=Og00RbR1g00S@R2790p=lf5R3f4R4f3R5f2R6'6'Bf1R7/00'v591p=C1h261L70'zp=51L671h02'zp=A1670=912p=J1067=910p=@1067/00p=?1s10p=3Au170p=;AY1709Y16p=1AY170p=DAY167/Z0p=dAu167=Y10p=W20810p=KP1P6P7P0H07p=7P6g00TER8g00TdR9P9g00UDR:P1P7g00S^R;P0C^g00UdR<Fip==P7P8P9P9P:P0J06p=p1}10p=8At167=o10p=SP1P7g00VDP0C^p=QP7P8P9P9P:P0P<Fip=:P1P7g00VkP0C^p=VP6P8P9P9P:P7P0K05p=[P5P8P9P9P:P6P7P0GXp=~At170p=cP1P6P;Ao170C^p=aP4P8P9P9P:P5P6P7P8P9P9P:P0P<FiGXp=bf6R<P8P9P9P:P3P4P5P8P9P9P:P6P7P0GXGXp=`P<P8P9P9P:P3P8P9P9P:P4P5P6GXP7P0GXp=>1v709916p=<A9170p=j1Z70,Z6p=TAo170p>0:1h20p>09P1g00WRR8#4R;#4R=#4R>#4$0FR?#|R@/n0S00%|>RA$0ERB$00RCg00XcRD#2RE#2RF/P0RG%4?S01#4R?#ORH#URI,07S02,N@,g@,PF39X;1P1100IRJ,n@S031n@7,PF=9CGX;1PCPC%OH#O#O#O#O#O#URH,00RG,NAS04,fB10JHRK,NAS05,fB%U>RL,qGS06,NAS07&01BRM5MBS081qKLS09,NAS0:=MBMS0;PBPC\CS0<&0ABRAPAQ04Q05Q0<\B/mAS0=%U?R?,FGS0>%l?RN#kS0?107HROP?POP?POP?EC[S0@1EO?S0A1L2?RP106HRQ/0?RR?5R?[S0B1GQ?S0C1L?2S0D105HRQ/0?RR=A?R[S0E1IQ?S0F104HRQ/J?\NS0G1HQ?S0H103HRQ?@?Q\NS0I16Q?S0JP1A?<H?S0KP1f7RQ??IH/F?S0LQ0?f8RR??IHRSP?PSP?PSP?EC[S0M1ES?S0Nf9RS??IHRT/0?RU?5U?\PS0O1GT?S0PQ0Df:RT??IHRU/0?RV=A?V[S0Q1IU?S0Rf;RU??IHRV/J?\NS0S1HV?S0Tf<RV??IHRW?@?W\NS0U16W?S0VP1f=RW/0I??H?S0WP1f>RX/0I/FH%lHRY#kRZf?R[/0IR\PHP\PHP\PHEC[1E\H1L2HR\f@R]/0IR^/0HR_?5_H[1G^H1LH2R^fAS0X/0IR_/0HR`=AH`[1I_HfB/0IR_/JH\Y1H_HfC/0IR_?@H_\Y16_HP1fD??IHP1fES0Y/FI%lIR_#kS0ZfFR`PIP`PIP`PIEC[1E`I1L2IS0[fGS0\/0IRa?5aI[Q0\/GI1LI2S0]fHRa/0IRb=AIb[1IaIfIRa/JI\_1HaIfJRa?@Ia\_16aIP1fKS0^/0IP1fLS0_/FHfMRaPHPaPHPaPHEC\Z1EaHfNRb/0HRc?5cH\\1GbHfORc/0HRd=AHd\^1IcHfPRd/JH\Y1HdHfQRe?@He\Y16eHP1fRS0`/0HP1g00X7Rf&048-031Rg%2FRh#2Ri#2Rj#2Rk#2Rl#2Rm#2Rn#3Ro';Rp%3mRm%3lRl%3iRi%3ERE,;gS0a1s1DRD31312021?S0b=r1DRq%2nS0c#3Rn1;gmRr%3jRj,;gS0d%3hRh%3FRs'D51l51p31g00YBRp'e3d1;gl1DED9Wgi51r1;gnS0e%3kRk1;gs,Di71j91om51q/ep5do&01fS0f5Mf3M&00fS0g%KRS0h&0D1Ro774%KTS0i?7<o776%KSS0j?73o%KUS0k?7Qo775777&0C1S0l&0B1RnPn1\1HRr1\12RE5=n,pnS0m&0@9R9%R=#8S0n%R;Rt#R#8Ru%R8Rv#8Rw5Sr5=nP9PnPn1\1IRx==nE,pnS0oP9Q0n%4t#8S0p%RvRy#8Rz5Sx5=nP9PnPnQ0mP9%8>R>%8tRt5Sr9=nzP9PnPn1\1?R{,QE,:nS0qP9%8;R|,VE,:n1Q|{,:n5[nC~S0rP9PnPnA=n{E,pnR}P9Pn%4vRv#8R~,c{=at|DbP9PnPnQ0qP91}18R8,VE,:n1Q8{,:n5[nC~S0sP9PnPnP}P9Pn%8=S0t,c{S0u=aw8DbP9A=n8|S0vF`F`F>F>F>20?n:S0wP0P6g00YnR:g00ZNR='m20>06=9:=dB0=127H0<S0xb=b>b?X01X31X41X51X61X71X81X91X:1X11X21g00ZnR2\YR=1BHU=<S5[P2\_S0y1BIU=<TR[1BHT=<SQ\=A533?\PP2\NR21B?TR:=<S<[A5<<?\PS0zA<S:Q\21jQR[[[[[[[^01^31^41^51^61^71^81^91^:1^11^21P0P6PSfTR:P]PRQ0\P[PbP7P`PaPQPXQ0YQ0^Q0_Q0`fSS0{OBb<bfbabQbPbObNbLbeb`bKbJbIbHbGbdb_bFbEbDbCbXbcb^bWbVbUbTbSbbb]bRbMbBbAb@9{GKG_PCPCQ07,fBQ0:,fBPMPMPBQ0<PAPAQ07Q0:Q0=Q06Q09P1%U;00;LR;,6G100;RAQ02/0H/qL/0;'jX;1P116K;16O;?@;AX;1Q0>Q0@Q0AQ0BQ0CQ0EQ0FQ0GQ0HQ0IQ0JP1Q0KP1Q0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VP1Q0WP11FR?S0WQ0?PSP?PSP?PSP?EC[S0?1ES?S0V10T?RA?5A?\PS0U1GT?S0TQ0D10U?RT=A?T[S0D1IU?S0S1JV?\NRT1HV?RAA@W?W\NRN16W?R;P110X?ROP1Q0WQ0?Q0VQ0UQ0TQ0DQ0SPTPAPNP;P1POP1Q0_/0I/FH10aIROPHPOPHPOPHEC\Z1EOH10bIRO/0HR;?5;H\\1GOH10cIRc/0HRO=AHO\^1IcH10dIRd/JH\Y1HdH10eIRe?@He\Y16eHP1Q0`??IHP1Q0{/FIQ0ZP:PIP:PIP:PIEC[1E:IQ0[fURe/0IRd?5dI[1GeIQ0]fVRd/0IRc=AIc[1IdIfWRd/JI\_1HdIfXRd?@Id\_16dIP1fYS0]/0IP1fZS0Z/FHf[RdPHPdPHPdPHEC\Z1EdHf\RZ/0HR_?5_H\\1GZHf]R\/0HR_=AH_\^1I\Hf^R\/JH\Y1H\Hf_R\?@H\\Y16\HP1f`S0S/0HP1Q0c#2S0c#2R\#2RY#2R^#2R_#2Rc#3RO%3YRY?1ji%3\R\91DY%2cRc#2R;#2RN#2RA#2RT#3%3NRN%3;R;Q0d,Dl315Wg%2T#2#3%3A,;gQ0e1Dml51\9WgN311;g;%3_R_/Dm51DQ0b=r1k%3c,;gRc71N91qi/ep,ZD5TD5TD5TD5TD3d%3^R^Q0a,Dh91ji71Y1;gO1;gk1Dih51m9Wg_51NQ0c#3,D\9Wg^91sOAWgYk91iOQ01#U-021=r1D?1si/ep,ZD5TD5TD5TD5dcQ0f5Mf5MfQ0gQ0h%KV774Q0i%KX77<776Q0j%KW773Q0k%K[77Q775777Q0lPnPnQ0mP9%Rv#8R3%Ry#8=Srw5=nP9PnPn1QEx,:nP91VEu,:n1Qux,:n5[nP9PnPnQ0oP9%4y#8=Sxu9=n3P9PnPnQ0mP9%4v#8=Sr~9=nuP9PnQ0rP9PnPnP}P9PnQ0p,c{=az|DbP9PnQ0sP9PnPnP}P9PnQ0tQ0n,c{;a8DbP9PnPnQ0qP91VE>,:n1Q>{,:n5[nP9PnPnP}P9AS{z>9=n~P9PnPnQ0qP91VEt,:n1Qt{,:n5[nP9PnPnP}P9Q0u00:t9=nwP9Q0vF>F>F>F>F`F`F>F>F>F>Q0wQ0xb=b>b?X01X31X41X51X61X71X81X91X:1X11X21XY1XZ1X[1X\11BH[RH=<W5\=Q0[A5VVI[Q0y1BI]=<[W[A<XHS\=Q0z1B?[R==<VQ\2A5QQ?\P1B?]RH=<UR\2A5]]?\PQ0X9<[H\2A5[[?\PA<X=]\21jVW[[[[[[[[[[[[^01^31^41^51^61^71^81^91^:1^11^21^Y1^Z1^[1^\1P0P6PSfbP]PRQ0\PbP:PeP[PdPZP7P`PaPQPWPXQ0YQ0^Q0_Q0`Q0{Q0]Q0ZQ0SfaOKb<btbrbpbobnbmblbsbqbkbjbibhbgbfbabQbPbObNbLbeb`bKbJbIbHbGbdb_bFbEbDbCbXbcb^bWbVbUbTbSbbb]bRbMbBbAb@Q09Q0fQ0gPoQ0l1\1L,VE,:nQ0wQ0xb=b>b?&09LP0b<Rn9yKLE]Q06AyGLnE]3{G_1mCMG_G_Q04Q085MBQ05Q0;5MB59Ce1PFG1PFK59CeQ00,PFQ03,PF59Ce1N@JRF,g@1x@JE]1N@0RJ,g@1x@0E]%wJ%wF59CeXu1o"). Qed.

(* [comment removed for export] *)
Lemma shl32_shr30 : forall x, 0 <= x < 2^31 -> (x ≪ 32 mod 18446744073709551616) ≫ 30 = 4 * x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_lp ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51zh62Hah74__x2h84__x3h91Hh:2H0h;2H1h<2H2h=2H3h>2Hxh?6__sat4h@6__sat5hA1qhB1rhC1xp;1p;2p;3p;4p;6p;7p;8g000kj10Tg002Jj16Tg004]j1?Tg006ij2MTg002hj24Tg003Dj2<Tg007Fj21Tg004=j25Tg006Ij2QTg007cj2>Tg008]j2vTg00IKj3ATg009>j1qTg00Naj2TTg009Wj2kTg00:>j2dTg001nj2RTg00:ej2aTg00;Kj2`Tg011lj2]Tg012Tj3\Tg00<1j1GTg00<Pj2DTg00?Uj2@Tg00@Aj2PTg001Pj1[Tg00>Kj2ZTg00>lj3YTg00=9j2OTg00=bj3NTg00@mj1XTg00AMj3CTg00Amj1WTg00BMj2FTg00Bkj4VTg00CIj1xTg00Cgj1wTg00DRj2UTg00E5j1uTg00G@j2LTg00Q6j6pTg00EWj3BTg00F:j3oTg00Gcj2jTg00HEj2hTg00H_j2eTg00Iej3cTg00JDj4fTg003_j1gTg0138j3bTg013[j3iTg000Mj6JTg00K6j1lTg00KTj3mTg005Bj2nTg00L=j3_Tg00O>j3^Tg00Ogj4HTg00PRj7rTg00R>j7sTg00QZj8tTg00S@R0f0R1'Rp=3%01#0p=S%01#0#0#0#0#0#0#0p=9g00RbR2f1R3;A1p=8A^231p=:1U21p=7P2P3g00VDP1CHp=EP3g00TER4g00TdR5P5g00UDR6P1g00UdFrp=2P2P3g00VkP1CHp=;f2R7P4P5P5P6P3P1Fsp=Kf3R8P4P5P5P6P7P3P1Gtp==P2P3g00S^P1CHp=I%31g00WRR9#0R:#6R;%?9R<#?#?R=#?R>#6R?'MR@,41'<RAP2%0:RB#0#SRC#6RD,M;,13RE%0C#9#9#9RC#SRF#9#9#9#9#6RG,51%0=#6R='Q%6BRB/17RH'8X52P215EGRE1M;='>181HX52P2%6FRF,13RI%6CRC,>1/8HX521vICAA2C0RH#q117FRJ1>JC,1C15JC'T'8[1kJC140CRJ118FRK/5CRL#314LC'<[1dKC14C0f4RL/1FRM/5CRN,4C1RN0'<[1aMCf5/1FRM/>C=A20\H1`MCf6/1FRM/5C/8M\H1>MCP2f7/1F/5CP21];?140;%3?140@[[%3;RMg014>RNA\;?3UW6%3@\N^6Mg00X7RMg00XcRN#GR@#GR?,D21D2@R@':1D2NRN/:@g00YBRO'@'P%G?,D2R?%[9,Z2=Y2@1O2C=N2N':':/@O%XMRP5CM3C%WMRQP21F27P31F28CV%x2RR%w2RSPS1U20RT%7CRU'E,2S%u5RV1L2<R<,;T,2S1E<U,2S5KSC=PVPSPSPSP4P5P5P61IUT,2SEpPV1L2:R:%7FR55B21L29R99B2U=o2<'I,2SC=PV%7B=B2:,I9,2SC=C=1jS6R6P1P7g00YnR:g00ZNR<'h1e17=A:<dAc203CfR0b1b2b3X42X72X82%38148C'<\Jg00Zn\H11C7/TL,8K[11B8,87[[^42^72^82P1P8f;PLf8f9O5b0b?b@bBbAb=b<b;b:b915IG1O2F=N2@/:N/@O1:N?/@O,PN=CMP5CMPQ1F23PRPS1;T9,2S%7;%g>5b2,E9,2S5KSPVAB295R9,;T,2S%7G,E9,2S5KSC=P6P0b1b2b3X42%3I14IG'<\A^42P1P7P3O2b09iIGEJ1QE=PPPQ%l2RIPR%7=,;T,2SP6P0b1b2b3%3=P1b09mE=EJ1n3DPPPQPIPR%7D,;T,2SP6P0b1b2b3%3DP1b09_3DEJW>XC2o"). Qed.

Lemma swrap32_u32 : forall x, bv_swrap 32 (u32 x) = bv_swrap 32 x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_bdt_lp ()) [] "h01zh17__arithh24__ffh38__varmaph45__with51xp;1p;2p;3p;4p;7p;6g014Zj19Tg000kj10Tg002Jj1<Tg00Naj24Tg004=j23Tg008@j25Tg003_j1?Tg005bj26Tg00IKj32Tg00HEj28Tg00@mj1=Tg00Amj1KTg00K6j1JTg00CIj1ITg00Cgj1HTg00DRj2:Tg00Ogj4GTg00PRj7DTg00Q6j6CTg00Gcj2BTg00H_j2ATg00Iej3@Tg00JDj4ETg015Qj4FTg000Mj67Tg016:j1;Tf0R0#0#0#0#0p=1%00#0p=>g00RbR1P1%90R2g00WR#0#1R3#>#1#1#1#1#1#1R4#<R5'4%04#<R4'3/55R6%?3R3f1R7'69210X01P11405/34R8/55R9%97/45/34/55=210X01P1P815051475/34/55521X0118191304/45/34P0P5P4g00X7R5#=%K5%J1%I1%H1R5g00TER8g00TdR:P:g00UDR;P5P8P:P:P;P11:14g00S^g00S@R:,:1CGg00UdFDEC1B5;P0f2R;g00YnR5g00ZNR8'81A0;=258dA@1:7CEb2b3b4A214:g00Zn[P0b1CFE7A2169e1630%;0E71632%;2E7W5o"). Qed.

Lemma shl1_mul : forall x, x ≪ 1 = 2 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma land1x : forall x, Z.land x 1 = x mod 2.
Proof. intros x. apply (Z.land_ones x 1). lia. Qed.
Ltac ck := let K := fresh "KC" in
  if_cases K; zify_cond K;
  [exfalso; rewrite ?land1x, ?zb_lxor_ones in K by lia; Z.div_mod_to_equations; lia | clear K].

Section LP.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (x5 x10 x11 x12 x13 x14 x16 x17 x21 x22 x23 x24 x25 x26 x27 x29 : word).
  Variables (m : fmem) (NC WK TD : Z) (nc : list Z) (tl M1 : Z) (jt jw : list byte).
  Variable POST : machine_state -> Prop.
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis HM1 : 1 <= M1 <= 256.
  Hypothesis HNCL : M1 <= zlen nc.
  Hypothesis HNCR : Forall (fun c => - 32768 <= c < 32768) nc.
  Hypothesis HJT : length jt = (4 * Z.to_nat (2^tl))%nat.
  Hypothesis HJW : (2 * Z.to_nat M1 <= length jw)%nat.
  Hypothesis HNC : 0 < NC /\ NC + 2 * zlen nc <= 2^64.
  Hypothesis HTD : 0 < TD /\ TD + 4 * 2^tl <= 2^64.
  Hypothesis HWK : 0 < WK /\ WK + zlen jw <= 2^64.
  Hypothesis DNT : NC + 2 * zlen nc <= TD \/ TD + 4 * 2^tl <= NC.
  Hypothesis DNW : NC + 2 * zlen nc <= WK \/ WK + zlen jw <= NC.
  Hypothesis DTW : TD + 4 * 2^tl <= WK \/ WK + zlen jw <= TD.

  Definition lp_W : list (Z * Z) := [(TD, TD + 4 * 2^tl); (WK, WK + zlen jw)].

  (* [comment removed for export] *)
  Definition lp_inv (m1 : fmem) (syms : list (option Z)) (snext : list Z) : Prop :=
    u8arr usegs m1 TD (tsym jt syms)
    /\ u8arr usegs m1 WK (u16s (map (Z_to_bv 64) snext) ++ skipn (2 * length snext) jw)
    /\ bytes_at usegs m1 NC (u16s (map (Z_to_bv 64) nc))
    /\ munch lp_W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  Hypothesis HAL : TD mod 4 = 0 /\ WK mod 2 = 0 /\ NC mod 2 = 0.
  Notation ST pc mm x7 x18 x24 hT s fm :=
    (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.lxor TD 18446744073709551615)) (Z_to_bv 64 (2^tl + -1)) x7 (Z_to_bv 64 s) (Z_to_bv 64 M1)
             (Z_to_bv 64 1) (Z_to_bv 64 NC) (Z_to_bv 64 (M1 - 1)) (Z_to_bv 64 tl) (Z_to_bv 64 WK) (Z_to_bv 64 (2^tl))
             (Z_to_bv 64 (Z.lxor WK 18446744073709551615)) (Z_to_bv 64 TD) x18 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 fm)
             (Z_to_bv 64 (2^(tl - 1))) (Z_to_bv 64 65535) x24 x25 x26 x27
             (Z_to_bv 64 (Z.lxor NC 18446744073709551615)) (Z_to_bv 64 (WK + 2 * M1)) (Z_to_bv 64 (bv_swrap 32 hT)) (Z_to_bv 64 M1))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition lp_ok (syms : list (option Z)) (snext : list Z) (hT fm : Z) : Prop :=
    length syms = Z.to_nat (2^tl) /\ Forall (fun v => 0 <= v < 65536) snext
    /\ 0 <= hT < 2^32 /\ (hT < 2^tl \/ hT = 2^32 - 1) /\ (fm = 0 \/ fm = 1).

  Lemma lp_loop : forall f s syms snext hT fm r m1 (w7 w18 w24 : word),
    lowprob_loop nc tl f s syms snext hT fm = Ok r ->
    Z.of_nat f = M1 - s -> 0 <= s < M1 -> zlen snext = s ->
    lp_ok syms snext hT fm -> lp_inv m1 syms snext ->
    (forall m2 syms' snext' hT' fm' (y7 y18 y24 : word),
       r = (syms', snext', hT', fm') -> zlen snext' = M1 -> lp_ok syms' snext' hT' fm' -> lp_inv m2 syms' snext' ->
       evt usegs POST (ST 0x1f2f4 m2 y7 y18 y24 hT' M1 fm')) ->
    evt usegs POST (ST 0x1f280 m1 w7 w18 w24 hT s fm).
Proof using All.
  induction f as [|f IH]; intros until w24; intros RL HF HS HL OK INV KONT; [exfalso; lia|].
  destruct INV as (TA & WA & NB & MU & WM & MI). destruct HAL as (TAL & WAL & NAL). unfold lp_W in MU.
  repeat (first [ ck | zstep; rewrite ?shl1_mul ]).
  assert (NR : - 32768 <= Znth s nc < 32768) by (apply (Forall_Znth (fun c => - 32768 <= c < 32768)); [exact HNCR | lia]).
  lazymatch goal with |- _ => let a := cur_mem_addr in
    pose proof (u16_znth usegs m1 NC nc s a NB ltac:(lia) ltac:(addr_tac)) as RD end.
  zstep. rewrite (zx16_short (Znth s nc)) by lia.
  repeat (first [ ck | zstep ]).
  if_cases K; zify_cond K.
  - assert (NM1 : Znth s nc = -1) by (Z.div_mod_to_equations; lia).
    cbn [lowprob_loop] in RL. destruct (bind_Ok_inv _ _ _ RL) as (c & LC & RL1). apply load_Ok in LC. destruct LC as (_ & ->).
    rewrite NM1, Z.eqb_refl in RL1. destruct (bind_Ok_inv _ _ _ RL1) as (syms1 & OS & RL2). apply ostore_Ok in OS. destruct OS as (HTR & ->).
    destruct OK as (SL & SNR & HT0 & HT1 & FM).
    assert (P2 : 2 <= 2^tl <= 4096) by (split; [change 2 with (2^1); apply Z.pow_le_mono_r | change 4096 with (2^12); apply Z.pow_le_mono_r]; lia).
    rewrite (swrap32_small hT) by lia. rewrite ?(Z.mod_small hT) by lia. rewrite ?shl32_shr30 by lia.
    rewrite SL in HTR. repeat (first [ ck | zstep; rewrite ?shl32_shr30 by lia ]).
    pose proof (u8arr_store_ok usegs _ TD _ (4 * hT + 2) (wa (TD + (4 * hT + 2))) TA ltac:(rewrite tsym_length; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (TD + (4 * hT + 2)) by lia
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (TD + (4 * hT + 2)) by lia
    end.
    rewrite ?le1_lit.
    pose proof (length_skipn (2 * length snext) jw) as LSK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?bb]) _) =>
      pose proof (u8arr_write usegs _ TD _ (4 * hT + 2) bb TA ltac:(rewrite tsym_length; lia)) as TA2;
      apply (u8arr_frame usegs _ WK _ (TD + (4 * hT + 2)) [bb]) in WA;
      [ | lia | cbn [length]; lia | rewrite app_length, u16s_length, length_map, LSK; cbn [length]; lia ] end.
    clear TA. store_done.
    replace (Z.to_nat (4 * hT + 2)) with (4 * Z.to_nat hT + 2)%nat in TA2 by lia.
    rewrite tsym_store in TA2 by lia.
    repeat (first [ ck | zstep ]).
    pose proof (u8arr_store_ok_n usegs _ WK _ (2 * s) 2 (wa (WK + 2 * s)) WA ltac:(lia) ltac:(rewrite app_length, u16s_length, length_map, LSK; lia) eq_refl) as SOK2.
    zstep.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (WK + 2 * s) by lia
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (WK + 2 * s) by lia
    end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bb) _) =>
      pose proof (u8arr_write_bytes usegs _ WK _ (2 * s) bb WA ltac:(lia) ltac:(rewrite ?length_le2, ?length_Z_to_le_bytes, app_length, u16s_length, length_map, LSK; lia)) as WA2;
      apply (u8arr_frame usegs _ TD _ (WK + 2 * s) bb) in TA2;
      [ | lia | rewrite ?length_le2, ?length_Z_to_le_bytes; lia | rewrite tsym_length, HJT, ?length_le2, ?length_Z_to_le_bytes; lia ] end.
    clear WA. store_done.
    replace (Z.to_nat (2 * s)) with (2 * length snext)%nat in WA2 by lia.
    rewrite snext_snoc in WA2 by lia.
    zstep. zstep.
    rewrite (swrap32_small (hT + -1)) by lia.
    pose proof (u32_range (hT - 1)) as U32R.
    assert (OK2 : lp_ok (oupd_nat (Z.to_nat hT) s syms) (snext ++ [1]) (u32 (hT - 1)) fm).
    { unfold lp_ok. rewrite oupd_nat_length. split; [exact SL|]. split; [apply Forall_app; split; [exact SNR | constructor; [cbv beta; lia | constructor]]|].
      split; [exact U32R|]. split; [|exact FM].
      destruct (Z.eq_dec hT 0) as [H0|H0]; [right; replace (hT - 1) with (-1) by lia; exact u32_m1 | left; rewrite u32_id by lia; lia]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (INV2 : lp_inv mm (oupd_nat (Z.to_nat hT) s syms) (snext ++ [1]))
        by (unfold lp_inv, lp_W; refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); assumption) end.
    step.
    if_cases K2; zify_cond K2.
    + assert (F0 : f = 0%nat) by lia. subst f. cbn [lowprob_loop] in RL2. injection RL2 as <-.
      replace (s + 1) with M1 by lia.
      replace (hT + -1) with (bv_swrap 32 (u32 (hT - 1))) by (rewrite swrap32_u32, swrap32_small by lia; lia).
      eapply KONT; [reflexivity | rewrite app_length; cbn [length]; lia | exact OK2 | exact INV2].
    + replace (hT + -1) with (bv_swrap 32 (u32 (hT - 1))) by (rewrite swrap32_u32, swrap32_small by lia; lia).
      eapply (IH (s + 1)); [exact RL2 | lia | lia | rewrite app_length; cbn [length]; lia | exact OK2 | exact INV2 | exact KONT].
  - repeat (first [ ck | zstep ]).
    assert (NN1 : Znth s nc <> -1) by (intro E; apply K; rewrite E; reflexivity).
    destruct OK as (SL & SNR & HT0 & HT1 & FM).
    assert (P3 : 1 <= 2^(tl - 1) <= 2048) by (split; [change 1 with (2^0); apply Z.pow_le_mono_r | change 2048 with (2^11); apply Z.pow_le_mono_r]; lia).
    rewrite (srai48_short (Znth s nc)) by lia.
    rewrite (slt_lit_rr (Znth s nc) (2^(tl - 1))) by lia.
    rewrite (Z.mod_small fm) by lia. rewrite (land_neg_b2z _ fm FM).
    pose proof (length_skipn (2 * length snext) jw) as LSK.
    pose proof (u8arr_store_ok_n usegs _ WK _ (2 * s) 2 (wa (WK + 2 * s)) WA ltac:(lia) ltac:(rewrite app_length, u16s_length, length_map, LSK; lia) eq_refl) as SOK2.
    first [zstep | step].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bb) _) =>
      pose proof (u8arr_write_bytes usegs _ WK _ (2 * s) bb WA ltac:(lia) ltac:(rewrite ?length_le2, ?length_Z_to_le_bytes, app_length, u16s_length, length_map, LSK; lia)) as WA2;
      apply (u8arr_frame usegs _ TD _ (WK + 2 * s) bb) in TA;
      [ | lia | rewrite ?length_le2, ?length_Z_to_le_bytes; lia | rewrite tsym_length, HJT, ?length_le2, ?length_Z_to_le_bytes; lia ] end.
    clear WA. store_done.
    replace (Z.to_nat (2 * s)) with (2 * length snext)%nat in WA2 by lia.
    rewrite snext_snoc in WA2 by lia.
    change (Znth s nc mod 65536) with (u16 (Znth s nc)) in WA2.
    cbn [lowprob_loop] in RL. destruct (bind_Ok_inv _ _ _ RL) as (c & LC & RL1). apply load_Ok in LC. destruct LC as (_ & ->).
    rewrite (proj2 (Z.eqb_neq (Znth s nc) (-1)) NN1) in RL1.
    assert (E15 : 2^15 = 32768) by reflexivity. assert (E16 : 2^16 = 65536) by reflexivity.
    assert (TS : to_short (2^(tl - 1)) = 2^(tl - 1)) by (unfold to_short; rewrite Z.mod_small; lia).
    zstep. zstep.
    replace (if Znth s nc <? 2^(tl - 1) then fm else 0) with (if to_short (2^(tl - 1)) <=? Znth s nc then 0 else fm)
      by (rewrite TS; destruct (Z.ltb_spec (Znth s nc) (2^(tl - 1))); destruct (Z.leb_spec (2^(tl - 1)) (Znth s nc)); first [reflexivity | lia]).
    assert (OK2 : lp_ok syms (snext ++ [u16 (Znth s nc)]) hT (if to_short (2^(tl - 1)) <=? Znth s nc then 0 else fm)).
    { unfold lp_ok. split; [exact SL|]. split; [apply Forall_app; split; [exact SNR | constructor; [cbv beta; unfold u16; rewrite E16; apply Z.mod_pos_bound; lia | constructor]]|].
      split; [exact HT0|]. split; [exact HT1|]. destruct (to_short (2^(tl - 1)) <=? Znth s nc); [left; reflexivity | exact FM]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (INV2 : lp_inv mm syms (snext ++ [u16 (Znth s nc)]))
        by (unfold lp_inv, lp_W; refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); assumption) end.
    zstep.
    if_cases K2; zify_cond K2.
    + assert (F0 : f = 0%nat) by lia. subst f. cbn [lowprob_loop] in RL1. injection RL1 as <-.
      replace (s + 1) with M1 by lia.
      eapply KONT; [reflexivity | rewrite app_length; cbn [length]; lia | exact OK2 | exact INV2].
    + eapply (IH (s + 1)); [exact RL1 | lia | lia | rewrite app_length; cbn [length]; lia | exact OK2 | exact INV2 | exact KONT].
Qed.
End LP.
