(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. From Stdlib Require FunctionalExtensionality. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module AsanPopFree.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_AsanPopFree () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr09K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PW0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5instr08c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PW1C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop06c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PW2C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PW3C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5instr0:c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PW4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PW5C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PW6C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PW7C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C46Stdlib5Lists4List:length_appI45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib7Mh_0112;AsanPopFree8pf_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00387CatExecDlength_Z_to_le_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C46Stdlib5Lists4List8app_nth1C47Corelib4Init5Peano2ltC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega6VarMap1t01K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z4succC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02C35stdpp7tactics<f_equal_helpC47Corelib4Init3Nat3subK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC46Stdlib5Lists4List8app_nth2K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z3maxI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_geI47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op204C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List;firstn_all2C47Corelib5Lists7ListDef6firstnI47Corelib4Init5Peano2le00C46Stdlib5Lists4List8firstn_0C56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List:firstn_appC47Corelib5Lists7ListDef5skipnC46Stdlib5Lists4List7skipn_0C46Stdlib5Lists4List:skipn_all2C46Stdlib5Lists4List9skipn_appC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2;pt_get_leafC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z3ltbC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C49OSSVerify5KrLib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z4lxorC59OSSVerify5KrLib?AxSymExec3Sound4AX2S;lxor_ones64C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SymExec:v_addi_litC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_rC49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec9step_srliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SymExec;step_sw_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5c_ltuC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C49OSSVerify5KrLib8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<step_bltu_tkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SymExec8btgt_litC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<step_bltu_ftC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib7Mh_0112;AsanPopFree8u64_of_ZC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto4kind02K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PD0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PD1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PD2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PD3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PD4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PD5C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PD6C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree3PD7C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00c59OSSVerify5KrLib7Mh_0112;AsanPopFree6pf_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_1_lc59OSSVerify5KrLib7Mh_0112;AsanPopFree7pf_iterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7mul_0_lC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6u_add1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8sub_diagC47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib7Mh_00387CatExec<wbytes_aboveC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFreeApf_wbytes_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExecBZ_to_le_bytes_wrapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFreeCword_to_le_bytes4_ZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree@pf_wbytes_insideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree<pf_mem_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree;pf_mem_cellC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S=rdn_pointwiseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z7div_addc59OSSVerify5KrLib7Mh_0112;AsanPopFree7pf_loopC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree?pf_bytes_lengthC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC47Corelib4Init5Logic6eq_symC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc59OSSVerify5KrLib7Mh_0112;AsanPopFree<pf_bytes_nthC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree@popfree_loop_runC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree=pf_mem_wbytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0112;AsanPopFree<popfree_specC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition PW0 : bv 32 := 0x00465713.  (* [comment removed for export] *)
Definition PW1 : bv 32 := 0xfff54793.  (* [comment removed for export] *)
Definition PW2 : bv 32 := 0x00150513.  (* [comment removed for export] *)
Definition PW3 : bv 32 := 0x00279793.  (* [comment removed for export] *)
Definition PW4 : bv 32 := 0x00f587b3.  (* [comment removed for export] *)
Definition PW5 : bv 32 := 0x00e7a023.  (* [comment removed for export] *)
Definition PW6 : bv 32 := 0x01560633.  (* [comment removed for export] *)
Definition PW7 : bv 32 := 0xff3562e3.  (* [comment removed for export] *)

Lemma PD0 : decode_any PW0 = Some (ShiftImm ALU_SRL 14 12 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"] "p;2p;1p;3p;4p;6p-1p10000p4p710p9p1000\p4p710p10019p4p710R0p8p1001Wp4p710P0p8p10022p4p710P0p8g002Qj2BTg0031j1ATg003Sj19Tg004Dj10Tg004ij12Tg005Nj15Tg005lj13Tg006Jj31Tg006mj48Tg007Yj47Tg0089j26Tg008[j34j1:Tg0095j4@Tg009Sj2?Tg00:0j6<Tg00:Hj2;Tg00:bj2=Tg00;@j3>Tg00;hR0g00<TR1'BR2#AR3g00=2#9R4P0P1g00=ng00>ZR5#0R6#2#5R7%25R5#2#0#3g00??R831%05R5#0#3=178%55%06#3R6;18C8P6C7,62R634R8P3P3%:3P0g00?[P1g00@LC@,?2P4P6E<R6g00@eR4g00AER2';1=86=442d3>o"). Qed.
Lemma PD1 : decode_any PW1 = Some (OpImm ALU_XOR 15 10 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"] "p;2p;1p;3p;4p;6p-1p10000p4p710p9p1000\p4p710p10019p4p710R0p8p1001Wp4p710P0p8p10022p4p710P0p8g002Qj2CTg0031j1BTg003Sj1:Tg004Dj11Tg004ij12Tg005Nj16Tg005lj13Tg006Jj34Tg00Aej49Tg007Yj47Tg0089j28Tg008[j35j1ATg0095j4@Tg009Sj2?Tg00:0j6<Tg00:Hj2=Tg00:bj2>Tg00;@j3;Tf0#2#2p=0g00;hR0g00<TR1'CR2#BR3g00BQ#:R4P0P1g00CMg00>ZR5#1R6#2R7#6R8%25R5#0R9#3g00??R:34%17#3=48:%15#1#6%09#0#0#0#3;4:C9%16#3C7,82R635R:P3P3%A3P0g00?[P1g00@LC@,?2P4P6E<R6g00@eR4g00AER2'=1>:6=542d3;o"). Qed.
Lemma PD2 : decode_any PW2 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"] "p;2p;1p;3p;4p;6p-1p10000p4p710p9p1000\p4p710p10019p4p710R0p8p1001Wp4p710P0p8p10022p4p710P0p8g002Qj2BTg0031j1ATg003Sj19Tg004Dj10Tg004ij15Tg005Nj13Tg005lj11Tg006Jj32Tg00Aej48Tg007Yj47Tg0089j26Tg008[j34j1:Tg0095j4@Tg009Sj2?Tg00:0j6<Tg00:Hj2;Tg00:bj2=Tg00;@j3>Tg00;hR0g00<TR1'BR2#AR3g00D9#9R4P0P1g00E5g00>ZR5#0R6#5R7#3%07#1g00??R732R8P8%55#0#0#3%15;27C8%06#1C7,62R634R7P3P3%:3P0g00?[P1g00@LC@,?2P4P6E<R6g00@eR4g00AER2';1=76=442d3>o"). Qed.
Lemma PD3 : decode_any PW3 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"] "p;2p;1p;3p;4p;6p-1p10000p4p710p9p1000\p4p710p10019p4p710R0p8p1001Wp4p710P0p8p10022p4p710P0p8g002Qj2BTg0031j1ATg003Sj19Tg004Dj11Tg004ij10Tg005Nj15Tg005lj12Tg006Jj33Tg006mj48Tg007Yj47Tg0089j26Tg008[j34j1:Tg0095j4@Tg009Sj2?Tg00:0j6<Tg00:Hj2;Tg00:bj2=Tg00;@j3>Tg00;hR0g00<TR1'BR2#AR3g00Ea#9R4P0P1g00F]g00>ZR5#1R6#0#5%05R5#0#0#2g00??R733R8P8%15#5%26;37C8%16#2C7,62R634R7P3P3%:3P0g00?[P1g00@LC@,?2P4P6E<R6g00@eR4g00AER2';1=76=442d3>o"). Qed.
Lemma PD4 : decode_any PW4 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"] "p;2p;1p;3p;4p;6p-1p10000p4p710p9p1000\p4p710p10019p4p710R0p8p1001Wp4p710P0p8p10022p4p710P0p8g002Qj2BTg0031j1ATg003Sj18Tg004Dj13Tg004ij10Tg005Nj1:Tg005lj11Tg006Jj32Tg00GIj47Tg007Yj46Tg0089j25Tg008[j34j19Tg0095j4@Tg009Sj2?Tg00:0j6;Tg00:Hj2<Tg00:bj2=Tg00;@j3>Tg00;hR0g00<TR1'BR2#AR3g00H5#8R4P0P1g00E5g00>ZR5#3R6#0R7#:R8%05#0#0#1g00??R532R9%07#1=285P9C7%36#1C6,52R634R9P3P3%93P0g00?[P1g00@LC@,?2P4P6E;R6g00@eR4g00AER2'<1=96=442d3>o"). Qed.
Lemma PD5 : decode_any PW5 = Some (Store SZ4 15 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"] "p;2p;1p;3p;4p;6p-1p10000p4p710p9p1000\p4p710p10019p4p710R0p8p1001Wp4p710P0p8p10022p4p710P0p8g002Qj2BTg0031j1ATg003Sj19Tg004Dj10Tg004ij11Tg005Nj15Tg005lj13Tg006Jj32Tg00I1j48Tg007Yj47Tg0089j26Tg008[j34j1:Tg0095j4@Tg009Sj2?Tg00:0j6<Tg00:Hj2;Tg00:bj2=Tg00;@j3>Tg00;hR0g00<TR1'BR2#AR3g00I]#9R4P0P1g00JYg00>ZR5#0R6#1#5R7%15R5#1R8#1#3g00??R932%08#3=279%05#0#5g00KE;29C8%06#3C7,62R634R9P3P3%:3P0g00?[P1g00@LC@,?2P4P6E<R6g00@eR4g00AER2';1=96=442d3>o"). Qed.
Lemma PD6 : decode_any PW6 = Some (Op ALU_ADD 12 12 21, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"] "p;2p;1p;3p;4p;6p-1p10000p4p710p9p1000\p4p710p10019p4p710R0p8p1001Wp4p710P0p8p10022p4p710P0p8g002Qj2BTg0031j1ATg003Sj18Tg004Dj10Tg004ij12Tg005Nj1:Tg005lj11Tg006Jj33Tg00GIj47Tg007Yj46Tg0089j25Tg008[j34j19Tg0095j4@Tg009Sj2?Tg00:0j6;Tg00:Hj2<Tg00:bj2=Tg00;@j3>Tg00;hR0g00<TR1'BR2#AR3g00Kc#8R4P0P1g00E5g00>ZR5#0R6#2R7#:R8%25#0#0#1g00??R533R9P9%07#2#1=385C7%06#1C6,52R634R5P3P3%93P0g00?[P1g00@LC@,?2P4P6E;R6g00@eR4g00AER2'<1=56=442d3>o"). Qed.
Lemma PD7 : decode_any PW7 = Some (Branch BC_LTU 10 19 8164, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"] "p;2p;1p;3p;4p;6p-1p10000p4p710p9p1000\p4p710p10019p4p710R0p8p1001Wp4p710P0p8p10022p4p710P0p8g002Qj2BTg0031j1ATg003Sj19Tg004Dj11Tg004ij10Tg005Nj15Tg005lj12Tg006Jj33Tg00L_j48Tg007Yj47Tg0089j26Tg008[j34j1:Tg0095j4@Tg009Sj2?Tg00:0j6<Tg00:Hj2;Tg00:bj2=Tg00;@j3>Tg00;hR0g00<TR1'BR2#AR3g00MK#9R4P0P1g00NGg00>ZR5#1R6#0R7#5R8%17#2g00??R733%16R6#0#0#2=387%05R5#1#0#5%05#0#0#0#0#0#1#1#0#1#1#2;37C8%26C7,62R634R7P3P3%:3P0g00?[P1g00@LC@,?2P4P6E<R6g00@eR4g00AER2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Fixpoint pf_mem (mem : word -> option byte) (e c s i : Z) (k : nat) : word -> option byte :=
  match k with
  | O => mem
  | S k' => pf_mem (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16))))
                   e (c + s) s (i + 1) k'
  end.

(* [comment removed for export] *)
Fixpoint pf_bytes (c s : Z) (k : nat) : list byte :=
  match k with
  | O => []
  | S k' => Z_to_le_bytes 4 ((c + Z.of_nat k' * s) / 16) ++ pf_bytes c s k'
  end.

Lemma pf_bytes_length : forall c s k, length (pf_bytes c s k) = (4 * k)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"] "h01kh11nh24__x1h31xh42IHh53IH0h67__arithh74__ffh88__varmaph95__with:1ch;4cstrh<5cstr0h=1sh>1yp;1p;3p;2p;4p;7p;6p;Bp;<p-1p10000p4p710p9g00O9R0p4p710g0019R1p4p710R2p8p1001Wp4p710P2p8p10022p4p710P2p8g004Dj1;Tg005Nj1bTg00OXj1QTg00P;j33Tg00Q<j21Tg00Q\R2j15Tg00R;j28Tg00:Hj26Tg00RRR3j14Tg00S2R4j27Tg00SOR5j29Tg005lj1<Tg00Slj2aTg00TIj2]Tg00UFj2:Tg008[j32j1DTg00U]j2VTg00V@j3UTg00V]j4OTg00WDj1@Tg00Wij2?Tg00XEj1NTg00Xej1MTg00YEj2LTg00Ycj1KTg00ZAj1JTg00Zlj2>Tg00[Oj2ITg00\2j3ATg00\Uj3ETg00]8j4HTg00]cj7GTg00^Gj2RTg00^ij2STg00_Uj3`Tg00`4j4_Tg00`fj4^TP1j6=Tg00aQj2\Tg00bZj3[TP0j3YTg00c7j4ZTg00cXlBFTg00d>l<XTg00dcl<WTg00eHR0f1R1f0R632p=0P0P0P0g00<TR7P7P7g00egP3P3P3P4g00fGf5R4f4R8f3R9f2R:P1P6MBFp=CP0P0P0P7P7P7g00fjP3P3P3P5g00gJP4P8P9P:P1P6MBFp=TP0P0P7P7P2P3P3P9g00gmP:P1P6M<Xp=PP0P7P6P3P1P:P9P8P4f6R3f7f8M<Wp=Bg00>ZR2#;#;R5#;R;#b#QR<A39:6'1g00hQR=#5#5#5#5R>/86'0R?X0018>=R@,60A3:1=,1</0@eP0%41R@/79,98%;;#<'aR;,]>R=,1<RAA3891RB,1<RC':%5:,8>RD,06X10P0P>A348:,1<,:6/0DX10P018>1RE1:>6/0DX101:>ERD%51RF,8>RG'0%<5R5175@RH'9RI%<2RJ,9@RK,75RL527%D0RM%D7RN%46927@10161V163UX>0X30ROPDPIP>P51675RIPEPHP>P5PIP1P@167@RDECRPETPGPLP>P5PIPFPK196JRKX37P1P@PDCPECM9B10CE%4CRD=27HR@PMPNPOPCPD167DPEPHPPM9BP6COP@%@:g00KER@%4:'?A3349,1<R3#@%43,?@g00i0R3#N%M31L71%K7%J7R3g00i\g00j;RPPPg00j[RPP71>75RH1I72R29A7H5E7g00k;1>7J9E729A7HCHg00kbFG1R3PP6P:g00@eRPg00AER3'61S6:=2P3dA`7@1C_b7b8b9X271756,95175K527^27P6%44O1b6b<b;b5C^PCP6E=PA1\>;E=A[<=B,1<AY<=BE=A389F,1</0GeX4?X00P6CZX00X=7X:7o"). Qed.

Lemma pf_bytes_nth : forall c s k j t,
  (0 <= j < Z.of_nat k)%Z -> (t < 4)%nat ->
  nth (Z.to_nat (4 * j) + t) (pf_bytes c s k) (Z_to_bv 8 0) = nth t (Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16)) (Z_to_bv 8 0).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"] "p'0h04__x1h14__x2h21Hh34__p1h42H0h53Ht0h67__arithh74__ffh88__varmaph95__with:4cstrh;4__x3h<5cstr0h=1ni001nh>2H1h?2Hjh@1xhA4__p2hB4__x4hC1jhD2z1hE1bhF1khG1thH2H2hI2H3hJ3Hj0hK2HthL4__x5hM1yhN1zhO2H4hP2H5hQ2IHhR6__sat0hS1chT1ei011ehU1mhV1qhW1rhX1si021shY2s0hZ2z2h[2z3p%0p&0p;1p;2p;3p;4p;<p;6p;8p;7p;Bp-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8g00lBR2p4p710P1p8p10022p4p710P1p8g00RRR1j14Tg00Q\j1@Tg00l_R3j2[Tg004Dj1iTg005Nk10bTg00OXk10]Tg005lj1uTg00P;j3ETg00m7k20MTg00m]j23Tg00n:R4j20Tg00V]j4fTg00nVR5j2PTg00:Hj2JTg008[j3;k10ATg00o1k30YTg00oWk10XTg00dcl<yTg0105k60RTg00WDj1_Tg010^k20OTg00SlR6j2Oj1qTg011Ok20NTg0120j1oTg00S2j25Tg012Ij2hTg00SOR7j21Tg012ik20yTg013Pk20xTg0147k20uTg014]k20qTg00XEk10mTg00Xek10BTg00YEj2kTg015Ck10iTg00Yck10eTg00ZAk10dTg00[Oj2jTg00Zlk203Tg015ak10cTg00^Gk20aTg00^ik20`Tg00_Uk30_Tg00`4k40^Tg016Cj1`Tg00bZj3eTg00gmk10\Tg016ak601Tg017=k20[Tg017]R8k20ZTg00TIj2Uk10LTg00Wik200Tg018=R9j1vTg00UFj2dTg018]j4Aj3pk20;Tg00U]k20UTg00V@k30STg0199j2sTg019[k10QTg01:9k20PTg01:Zk20>Tg00`fj4mTg004ik10KTg01;Cj8MTg00Q<k20?Tg00aQk209TP0j6Wk70ITP2k60JTg01;`j2tTg01<7k20HTg01<`k308Tg01=Ij2RTg01>5R2k20GTg01>MR0k207Tg00]8j4cTg01>ik60tTg00c7k40rTg00d>m<0FTg01?Fk40pTg00]cj7lTg01?dk60oTg01@Hk805Tg01@lk20lTg00cXmB0DTg01AIk20CTg01Ack30kTg01BLk306Tg01C5k20jTg01Cak304Tg00\2k30nTg01DAk70ETg01Dek70hTg00\Uk30gTg01EIk30fTg01Elk60sTg00KER:f0R;+00p=2f2R<f1R=/0;'Pp=C15<=#v/d;p=T13<=/5;p=\11<=/O;p=Nf4R>f3R?1U<=P;CAp=Kf5R@P>P?P<P=CA;;;p=Dg00<TRA/J;p=>g00eHRBPAP3P1P4g01FPP@P>P?P<P=P;M<yp=gPBPAPAPAP1P1P?P<P=g00hQR3P:P;N<0Fp>0V13<=/5;,1?p==A;A;:p=8A;A=;p=710:;p=6200;:p=LPAP<P=P;H0pp=ZP<g00i\RCg00j;RDPDg00j[REPAP=g01G2RFP;Ccg00kbRGFlp=aP<PCPDPDPEPAP=g01GYRHP;CcPGFlp=zP=PCPDPDPEP;J0op=xf6RIPCPDPDPEP@P>P?PCPDPDPEP<P=P;L05L05p=H15=;,1<p=<1O=;,U<p>02P?P<P=P;CA9;@>p>0W20l:;p=:PAPBPAPAP9P>P1P?g01H@P<P=P;N<0Fp=~PBPBPBPAPAPAg00fjP1P1P1P7g00gJP@P>P?P<P=P;NB0Dp=}PBPAP;P1P=P<P?P>P@PIf7R7f8R9M<yp>0@A;A?<,P>1P=;+0Cp=Q20>A;p=FB0kA=;p=]B06A=;p=Bg01Hm-0j;p=?g00i0RJ@04=;p>0=B0nA=;p=VPAP=PFP;Ccp=rP?PCPDPDPEP<PCPDPDPEP=PGFlP;K0Ep=IP<PCPDPDPEPAP=g00k;P;CcPGFlp=9P<PCPDPDPEP=P;K0Ep=|P<PCPDPDPEP=P;K0hp=bB0gA=;p=SP?PCPDPDPEP<P=P;L05p={1P=;-0C<p>0<13<=/3;p=^B0fA=;p=GPAP>P6P6P?P<P=P;GMp>0:PBPBPBPAPAPAg01IYP1P1P1PIg01J9P@P>P?P<P=P;NB0Dp>0TB06A=;:06A<p=YB04J=;:04J<p=XPAP=PHP;Ccp=nP=PCPDPDPEP;J0sp=wPBPAP2P1P0g01J`P@P>P?P<P=P;M<yp>0wP=PCPDPDPEP;PGFlp>0v%2=RG%4<RC7C=%@3R0#@S00#@S01#@R1,[=R2g00>ZRH#iRF#iRK#iRL$0bRM$0]RNPN%uKRO?T?<S02AE7I>20MM:RMPNP<P1%4>RP%uHRQ'3?\?I%iL#uRL5N7PMDKED[[^GB^CAS03XFB%43RR9CG=1[<110CORSP<PC%>CP1PO%>ORCEgP;CfPS%2>RS10>RRT'PACS>:RUPSPTPSP;X@ARTP:O1RV,0>p-0RW/JSA;WSSe:0YSSPAPAP4PTP410=;$0XXMAX@AP>P>%>>PRPVPTPT%4;RV#>X@B1JA:H0VM<yJ0RP<CfPU%_>%2Pf9RP13RQRRPIP9C=RU00OL%2U%2Lf;RUPRP9f:R4C=RX/OLRY#2[[P4PRP7PPC=00NL%8LRZ#o15LY1hXL'1,7X[20yXL%6Lf<RXPRPPPUC=RY/hLR[#2?C[L[20xYL10L:f=RYPRP4PXC=R[/hLR\,0L%L\'P[20u[Lf>R[PRPUPYC=R\/OL#8\Z20q\Lf?R\PRPXP[C=R]/hL/7]\Z1O]LPAf@R]PRPYP\C=/hLPAP5%2[S0410[:PNPNATO\[fBRRfARZ;E3PMPNP[P1P<PMDKEDPP%2]S0510Z:&0mJR^&0BJRJ1kA=&0iAR_7Z=&0eAR`&0dARa1jAFRb203A:Rc5aa&0cDRDPaAzacbS06PD1xa?FH20aaEREP;P<g00@eRdg00AERe'J20`;<=;dedB0_A:=H0^Reb7b8b9X0AX3W10;:P?\G[^0A^3WP;PNPNfCRd=TORfFS07fERf;E3PMPNPRP1PIPMDKEDPdP=P<O4b6WPWOP=P;O2n2001000000120000000bWbVbIbHb>b4b2bRb:bJb5XK2W?XGBXCAQ03%@?#49CG=PA%4@#`RGPNPNATO>?%4IRg=<P9>021LAEP9I5eNPMPNP?P113;Q?\>9=NPLPMDKEDXNAPA%@@S08#4S09ACS>;XNAP=PG&0\@S0:J01%2?S0;?C?G20[>:%8>RG%oG+0ZP8%8@S0<Q0<#oPNPNATOI@%49R8=<U4>021LAEU495eNPMPNP@P1%`8/3Q?\I4=NULPMDKEDP;%8IS0=PAP:%2;%44Rh#`S0>7C;PNPNATO=9%4URi=<[YS0?/OLS0@,U1RjAE[YUS0A5eNPMPNP9P1%`i/3QS0B?\=Y=N[LPMDKED]?XCA200::Rk%4PRl#`#6'PPNPN15O:Rm#vS0C/d7Rn15hX=NYLS0D,U1RoPMCAPNP;PNP9P[Q0BP:PYC=Rp/OLS0E,U1RqPMJ0WXENA;B7nRr%47Rs%:mRt/1sRu'7&0ABS0F&0AAS0G%4=/7VA;B=;20U=;40SXMBX@BS0HP7Ps%>sRVPnPuQ0CPtPT%:;X@AS0IPmPm%>mD~P7PsPVE}S0JN90@1[71S0K10sORvP7PsPVP1POPCEgS0LP@CfRVPv%_URs%2iRw%_PRx%2lRy1s:mS0M%6mRzPtPm%LmS0N%8tDQS0OPtPAP5Pk%4\S0P/1QS0Q#6S0R%4YR{11={S0S'7P@%4RS0T/1QS0U#6S0V&0QH-0PAR|%F0R0']20>A3R3'B#?00=^PJ1kA<S0W?Z=_S0XP`PaPaPa203AOR}/Vc,rc1xa>CIS0Y1xa@S0ZA9abcS0[5|a5baPD1jAHR~1Sb~59aC{PEPeb7b8b9X0AX1AX3WXAW1Pz<S0\%8=80<?11<=,7=[^0A^1A^3W^AWP;Q0N17@mS0]P@%4ZS0^PIO5b6W4X2kP=P;O2n2001000000121000000bDb>b<b:b5CmPrPBP9PNPNP;%4XRr=<\[>021LPMPNPPP1%`r/3Q?\:[=N\LPMDKEDX=BPNPNApN9jApN9qPMPM&0BNRmPN\NS0_20;N9RzPzPjPqQ0_\mS0`/JzPAPm&0L1RzPzQ0@Q0EPm\A/JzS0EPAPAQ0?#q%qpPLPLPA\AS0@Q0?PpQ0@\A/J6S0?1[91108OR6P9P8%>8P1POPCEgPICfP6%_X%2r%_4S0a%2hS0bP5Pk%4[R6/1QRp#6Q0P=<RZQ0Q?^Q:=<RZ'7P>Q0^/1QS0Q#6P^PJQ0W1kA?Rq7Z=S0WP`&0KHS0c,jARH,Vb,S~203AQRj,SbS0d/GjS0e/Gc/VH,S~59aPEPeb7b8b9X0AX1AX;AA<;=<P;11=Q/3QS0fP:P<C='7^0A^1A^;AP;Pf%4dQ07O3b6W4X2kP=P;O2n2001000000120000000b<b:b5I0:%>LS07GMGMGM1JNMS0gGMQ0C/d9S0CP;J01b2PNPnAEYX4S0h9eNoPMCAPNPoQ0hPMPnPBP1Q0C/[;X=B1[n110uOPnPuQ0JP1POPCEgPVPvPsPwPxPyQ0MQ0OPtPAP5PkQ0RQ0S/0OP@Q0VQ00#FS001B03S0S'B#?00=^PJQ0XP`PaQ0YQ0ZA9a~cS0R5|a5baPDPaAaab}PD1S~bS0Y=aa}FHPEPeb7b8b9X0AX1AX3WXAWQ0\%8;S0O80<?10<O11<?/0O[[^0A^1A^3W^AWP;Q0NQ0]Q0^P@PIPPO6b6W4X2kP=P;O2n2001000000121000000bDb>b<b:b5Cm20?NoQ0D-091EWJ0JEWW?P7P;P?K0IWTP;O1Q0=#oPNPN15O7Ro#vS0D/dIRk15lU=NXLS0V,U1S0^-0?NS0]'tAEXUPS0NPMCAPNP7Q0>?^Q9=<YXS0>/OLS0\,U1RlPMCARt9;N;XENPBP1PNPNATO97Ru/t;Q0hPMPtEDX=B137Q,5ORt#vS0M/dIS0J1tk1S0C5;BS0i%:tS0j/1gS0k%:oS0l/1gRn/3O#:S0m'7Q0FQ0GQ0HQ0JQ0kQ0MQ0jPTQ0IPtPt%>tD~PIPg%>gRtE}Q0CQ0m13=;#:XUAX=APkPnQ0DQ0lPTQ0IPoPo%>oD~PIPgPtE}S0IP1POPCK0TN90@1[I110gOS0lPIPgPtP1POPCEgP>CfS0DQ0lQ0aQ0b%_9S0m%28S0C15O4R8,s:S0j%68%:8RtP8%L8%8tDQS0M15OU#:S0kPA11;i/3ORt,s:%6t%:tR8Pt%Lt%88DQ11=rS0J/3O#:PA13[Q,5ORr,s:%6r%:rR:Pr%Lr%8:DQ13\Q,5O#:PAP5Q05Q0U,0]%4]R:,1=/7?PX%2R%4f/1Q,0d%@1Rd#FS0U20HAOS05Q00608AS00'B#?RR%@dRd#@Rr#@S0H#FR8%FrRr%FdRd,]|%F1Rt,]|S0G/B3Rg3YRo'BS0FQ0S#?,RdRT'R1]|81Bdg7Yr%uF-0HA>08A3Q0U5Y0#?,Rd'R1]|r1Bt37YdRdQ05>08A3RFQ0H#@#FRg'B#?'R1RoT%?o%?d1]|gAYrt05YF#?,RgQ0F#?;X^3X9XRR3X3X7XRPJ1kA>RR1kA@7Z<?Z=qP`PaPaPa1jAKRK/Gj,V}Rg,rcA9a~gCIPaPa1ngcQ0RCI5baPDPa1xa7Q0c#i,jARg/Sb/G}RF99aH5|aPaPa1nFcA9aHcRFCI5baPDPaPaPa1V}KRr,rcA9agrCIPaPa1nrcA9agcCI5baPDPaQ06PDPaA9aKc,waPDPaAzacKPDQ0Y=9aHFHFHFHPEPeb7b8b9X0AX1AX;AXBAXLAX3W13?QRg,5ORr#6P;Pr%LrQ0ODQPIP?11@</3ORr%Lr%8?DQ15O@Rr#6PIPr%LrQ0=DQ%87g01KBRr[%2911I7/79[[\S[[[^0A^1A^;A^BA^LA^3WP;fDRS#4R0,1P/3O#6PPPfP7P0P@PIP9P4PUP[P<O<b6W4W2P=P;O2n2001000000121000000b[bIbZbHbDb>b<b:b5CmQ0iPB139QR0=TO7R|PNPNP;Q0APMPNP9P1Q0B?\PY=N[LPMDKRdEDX=BPNPNP7A^hQ0=<YXRh/OLRo,U1R8PMCAA;N;dXENPNPNApN78ApN7lPMPMPmQ0_20;N7RdPdP8PlQ0`/JdPAPmPzPzPoQ0\Q0EPAPA%qhQ0>#qPLPLQ0@PhQ0>Q0?PVPvPsPwPxPyP5%2URh11{Q,0URU13XQR{9^6Q=<Z]A^pQX=<Z]'7P7%2YRY11:Q,0[R[P^PJAZR<_?Z=qP`1Gbj1GHj'G/VK,S~Q0e/GH/VK,S~59aPEPeb7b8b9X0AX1AX;AXBA13<Q9^=Q=<;?P;Q0fP<P?C='7^0A^1A^;A^BAP;PSP]Q0TPfO4b6W4W2P=P;O2n2001000000120000000b<b:b5I0:Q07GMGMGMQ0gGMPNP|Q0hPMCAPPP0P7PVPvPsPwPxPyP5PhPU%2{?C{6P7P^PJQ0XP`PaQ0R,waPDPaQ0d9aa~PDPaAzac~PDPaPa1G~jRj,ncAaajbCIC{FHPEPeb7b8b9X0AX1AQ0OPr[11<Q,0=%2<Rj%2g?Cg>[[[^0A^1AP;Q0TP]PPP=P<O5b6X4[X2YP=P;O2n2001000000121000000b<b:b5Q0KPvQ0LPVPvPsPwPxPyP5PhPU10iOP7P^PJQ0XP`PaAaa~}RiPDPaQ0[,waPDPaQ06PDPiC{FHPEPeb7b8b9X0AX1A10;O%8<Pr[Q0;10?O[[[^0A^1AP;P]Q0PP7PPP<O5b6X4[X2YP=P;O2n2001000000120000000b<b:b5CmO4EW1tu1P;J01b2Q0]Q0V-091RYEWPNPkQ0^Q0N5eNPMCAPNQ0^Q0NPMPkPBP120Gu;X=B20Gk1207nOPkPnQ0IP1POPCJ0wQ0DQ0lQ0aQ0bQ0mQ0CQ0jQ0MQ0kPAP5%2X10XpQ0J007OP9Q04Q0Q,0\Q00,Bt#?Q0GQ01#F;Y3/RT;X^PJQ0WP`PaPaPa1V}HR`,rcA9a~`CIPaPa1n`cQ0ZCI5baPDPaQ06PDPa1waFPDPaAzacHPDPAQ0Yg01K_P}Cc-0vaFHFHPEPeb7b8b9X0AX1AX;AX3W15O<Re#6P;Pe%LeP?DQPr\G%2@11>@007O[[\j[^0A^1A^;A^3WP;Q0<PZP:P@PIP7P4P<O8b6W4W2P=P;O2n2001000000121000000bDb>b<b:b5CmQ0]PYEWJ0tEWWJP;O1n200110200021110111100bYb?Q09Q0:EWPNPNQ02Q089E97PMPNP<P1Q09/3Q?\?7=N9LPMDKEDeXK2W?XGBXCAWQXFBP;H0rXFBXXAXSAo"). Qed.

(* [comment removed for export] *)
Lemma pf_bytes_cell : forall c s k j,
  (0 <= j < Z.of_nat k)%Z ->
  firstn 4 (skipn (Z.to_nat (4 * j)) (pf_bytes c s k)) = Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"] "p'0h04__x1h11Hh24__x2h32H0h47__arithh54__ffh64__p1h78__varmaph85__with91ni001nh:4cstrh;4__x3h<1lh=2Hjh>1xh?2H1h@4__x4hA1jhB1khC2H2hD2H3hE3Hj0hF4__p2hG1yhH1zhI2z1hJ2H4hK2H5hL2IHhM6__sat0hN1chO1ei011ehP1mhQ1qhR1rhS1si021shT2s0hU2z0hV2z2hW2z3p%0p&0p;1p;2p;3p;<p;6p;4p;8p;7p;Bp-1p10000p4p710p9g01LFR0p4p710g0019R1p4p710R2p8p1001Wp4p710P2p8g01LdR3p4p710P2p8g00RRR2j14Tg004Dj1hTg005Nk10sTg00OXk10aTg00Xek107Tg00Q\j1BTg005lj1qTg00S2j21Tg018=R4j1DTg00P;j3FTg00n:R5j25Tg00nVR6j2MTg00:Hj2WTg008[j33k105Tg00o1k30\Tg00oWk10ZTg00dcl<nTg0105k60RTg00V]k40NTg00m]j20Tg010^k20HTg00SlR7j2Jj1fTg011Ok20FTg0120j1eTg012Ij2\Tg00SOj26Tg012ik20ATg013Pk20>Tg0147k20rTg014]k20qTg00TIj2Qk10ETg00XEk10;Tg00YEj2lTg00Yck10gTg00ZAk10eTg00[Oj2`Tg00Zlj2{Tg015ak10`Tg00^Gk20_Tg00^ik20^Tg00_Uk30]Tg00`4k40[Tg016Cj1XTg00bZj39Tg00gmk10YTg016aj6vTg017=k20XTg017]R8k20WTg00WiR9j2RTg00U]k20TTg00V@k30STg00WDj1rTg0199j2iTg019[k10QTg01:9k20MTg01Acj3dTg01:Zk204Tg00`fj4kTg01MDj3>Tg00Q<k201Tg01;`j2ZTg004ik100Tg00\Uj3]Tg01;Cj8^Tg01McR:j2jTg015Ck10DTg00aQk202TP1j67k70OTP3k40CTP0k20BTg01N=k20JTg01IYR0k20KTg01NZk10LTg01O?k40@Tg01O^j3ETg01P<k20?Tg01<7k20VTg01<`k306Tg01=Ij2pTg01PXk40oTg01Q7k40nTg00c7k40lTg00d>m<0:Tg00]8j4oTg00]cj7mTg01?dk60iTg01@Hj8zTg01@lk20hTg01AIk209Tg01BLk308Tg01C5k20fTg01Caj3yTg00\2k30dTg01DAk70<Tg01Dek70cTg01?Fk40jTg01EIk30kTg00cXmB0bTg01Elk60mTg00KER3f0R1'Rp=2f2R;f1R</51'Mp=C10;</01p=[f4R=f3R>11;<'6/J1'Qp=<f6R?f5R@AE>;<7>=;31p=Hg00<TRA/W1p=Sg00eHRBPAPAPAP2P2P>P;P<g00hQRCP3P1N<0:p>0U10;</11,6>p==A3A13p=@A3A<1p=?1531p=81R13p=GPAP<g01G2P1Cop=TP<g00i\RDg00j;REPEg00j[RFP1g00kbRGFmp=xP;PDPEPEPFPAP<g01GYRHP1CoPGFmp=bP<PDPEPEPFP1J0ip=wP?PDPEPEPFP@P=P>PDPEPEPFP;P<P1GzGzp=a11<1,6;p=u20h31p=:PAPBPAPAP4P=P2P>g01H@P;P<P1N<0:p=tA3A>;,M=1M<1+09p=N204A1p=OB08A<1g01Hm+0fp=Ag00i0R4?y<1p>0IB0dA<1p=LP>PDPEPEPFP;PDPEPEPFP<PGFmP1K0<p=IP;PDPEPEPFPAP<g00k;P1CoPGFmp=;P;PDPEPEPFP<P1K0<p>03P;PDPEPEPFP<P1K0cp=cP>PDPEPEPFP;P<P1Gzp=g1M>;1M<1+09p>0G10>;/0</11,6=p=UPAP;P<P1H0jp=VB0kA<1p=KPAP=P7P7P>P;P<P1G^p=~PBPAP:P2P9g01QUP@P=P>P;P<P1M<np=}16;</J1p>0PA>>;<=3=1p=sPBPBPBPAPAPAP0P2P2P2P?g01J9P@P=P>P;P<P1NB0bp>0=B08A<1p=PAy4<19y4;p=YPAP<PHP1Cop=_P<PDPEPEPFP1J0mp=|AE;<19>=>p>0p%21RD%4<RH7C1g00>ZR0#hR9#hR:#hRG$0s$0aRI$07RJPI%BCRK#BS00#BS01#BRLPI%q:RM/1<RN#DS02AF@=;PLP@%4;%q0RO;[<P=%hG#qRGD<FH[^AAS03XBB%4CRP9CD1%2<RQ15<PRR'MACQ<3RSPQPRPQP1X>ARRP3O1RT,5<p-0RU/WQA3UQQe:0\QQPAPAP5PRP515<1$0ZXGAX>AP<P<%S<PPPTPRPR%41RT#SX>B1WA3R5H0UM<nJ0RP1H0NPSP@10PORPP;P=C=RS00HG%2S%2Gf7RSPPP=P?C=RV/JGRW#2[[P?PPP>P@C=00FG%@GRX#e11GW1\VG'6,?V[20AVG%8Gf8RVPPP@PSC=RW/\GRY#2?CYG[20>WG15G3f9RWPPP?PVC=RY/\GRZ,5G%GZ'M[20rYGf:RYPPPSPWC=RZ/JG#@\X20qZGf;RZPPPVPYC=R[/\G/?[\X1J[GPAf<R[PPPWPZC=/\GPAP6%2YS0415Y3PJPIPLPI11MZ#Df>RPf=RX;FC1QL;FHPV%2[S0515X3&0;4R\&074R41lA<R]&0gAR^&0eAR_1`A0R`1{A3Ra'T,x_&0`EREP_Ab_a`S06PE1w_>RbFa20__FRFP1P;g00@eRcg00AERd'W20^1;=3cddB0]A3<H0[Rdb5b7b8X0AX6U1513P>\Q[^0A^6UP1PJPIPLPIf?Rc,1M#DfBRefARf;FC1QL?FHPcP<P;O4b4WKWJP<P1O2n2001000000120000000bRbQbDbCb?b3b1bMbEW=XAAQ03%B;#49CD1PA%4>#XRgPJPIPLPI11M;#DPLPS%4=P?PGD<AFS?=59IPLPSA[1O;P?PGD<FHXHAPA%B>S07#4Rh%2;S08?C;1XHAP1Pg&0Y>S09EvACQ<g20X;3%@;Rg%eg+0WP8%@>R8%e8PJPIPLPI11M=R8#DPLPW%4?RQPVPGD<AFWV?59IPLPW%XQ?[O=PVPGD<FHP1%@=RQPAP3%4VRi#XS0:9CD1PJPIPLPIQ02%4WRD=u[ZRj/JGRk,QLRlAF[ZWRm59IRnPLP[%XD/0ORo/0<PZPGD<FH]=XAA1R33Rp%4SRq#XS0;#8'M11M3Rr#DRs93BCRt%:rRu93A3PBPA&05BS0<P2&05AS0=1?HTA3B<120T<140SXGBX>BS0>PCP3P5PsPuPR%:1X>AR5PrPr%SrDtM<n%rVS0?%2iS0@1i3r%8rRTPuPr%GrRH%@uDNPuPAP6Pp%4ZRu/6ORv#8A3A3<RwP>%4PS0A/6ORx#8&0Q0-0MARy%OKS0B5dA204ACRK'A00I\P4P]P^P_P_P_1{AMR]/La,TaPbCI1w_=S0CA;_`aRb603_5c_PEA;_a`CgPFPdb5b7b8X0AX6UXFUPTP<P;%@1RTH0GPw[^0A^6U^FUP1PH1?@rP@P?O4b4W?X1pP<P1O2n2001000000121000000bUb3b:CkPtPBPCPJPIPLPIP1PLPX%4YRtP[PGD<RrAFX[YRH59IPLPX%Xt?[O3P[PGD<RwFHX9BPJPnA>IL1Rz=3JwX<JPJA>ILlR{201IlR|,ZL=>Im59IA3J1wX<JR}PBPLA>ILrRr1ZL1=>IH59I=3JwX9BPBPCA>I1H99Ir=3JwX9BPJ&0;IRHA9Ir1=3JwX<JPJP{P}PJPlP}PAPJ&0ELR}P}PkP[PoP3PZC=Rw/JGPJ\A/W}S0DPAPA%fj%fwPGPGPA\AS0EPjPwQ0E\A/W7S0F%rWS0G%2DS0HP6Pp16tOR7#8RwAuPuXPPPvPOP3PXDU'?P;%4X/6OS0I#8RvP\P41lA;Ru1lA>S0J7V<P^1`A9Rj&000,`AR0'L9]A`1{AORr9]AjS0K/KrS0L/Ka/L09]A`5;_PFPdb5b7b8X0AX2AX;AAu1<;P116<O/0OS0MP3P;C='?^0A^2A^;AP1Pf%4cPeO3b4W3X1pP<P1O2n2001000000120000000b:D~%SGS0NG^G^P{PIPLPlPBPL1j1LX9B1jLL1RMMRePLPM%SMR~PLPMP~E}Q0GQ0HP6PpPwPeP;P\P4&0DARwP^Ab_]]PFPdb5b7b8PeP1b4X3vX1pP<P1O2n2001000000120000000b:CkP|202LkRkE7H0CE7A9I{H20BI{E7A>ICm20JImE720KLL&0LLE7P|PkE7A>ILnPIPLPlPmH0@E7AEICn20?InE7PsP1Evb1W=P@P1P>K0OWOP1O1%eQPJ11M@RQ#DRs11qW>0PYGS0H,QLRn5EIS0G201InRC,ZsAFYWSRl5EI59IPZQ0:POP?PYDURk/JGS0:,QLR|93JzX<JPBPLPJPIPL11M?Rz#DR{PLPZPiPYPGD<5EI1Z{1AFZYVRp5EI59IP|DsX9BPJPHPJPIPL1Z{LS0O=EIp99I1P|DsX<J10@O,1MR|#DS0P1ZsLRv53BS0Q%:|S0R%:QRe/0M#:S0S'?PBPAQ0<P2Q0=Q0>Q0PQ0RPRP5P|P|%S|DtPvQ0S10<1#:XPAX9APsPePRP5PQPQ%SQDtS0SPLPMP~K0=M<n%rSS0R%2qS0P1i3zS0>%8z%:zRqPz%Gz%@qDNS0=11MS#:S0<PA101MRq,i3%8q%:qRzPq%Gq%@zDN10<M#:PA10YO,1MRz,i3%8z%:zR3Pz%Gz%@3DN10ZO,1M#:PAP6Q0515[x1?<>PY%2P%4f/6O,5c%OLRc20VAMRPQ00#O606ARx'AR3%BLRz#BRq#ORQ9dAyR51PcK'AAdAycRR/PK,AQ%OzRzQ01#OR|'PB06APKRP%BqRq#B#O'A'pR21P|K,Pc,A5AdAy|/PKRy,PR,AQ%Oq1PQR,AP'pRP?YP\3Y7Y23Y7Y3P41lA=R3?V>w9Vu<P^P_P_P_1K0rR2,L]RP,TaA;_`PCIP_P_1_PaPbCI5c_PEP_P_P_&009,`AR9/K]RP,TaA;_jPCIP_P_1_PaA;_jaRPCI5c_PEP_1w_?1L]0RR9;_9603_P_P_1_RaA;_9aCI5c_PEP_A;_0a,|_PEP_Ab_a0PEA;_`jCgFaFaPFPdb5b7b8X0AX2AX;AX@AX6U10;OR9,1MRR#8P1PR%GRPTDN10=MRR#8P;PR%GRPgDNP?P@P8%G8%@@R8DNg01KBRR\8%2?1?@?[[[[[^0A^2A^;A^@A^6UP111Mf#8PWPfPSP@P?PVPYP[P;O:b4W3W1P<P1O2n2001000000121000000bWbDbVbCbIb?b:CkQ0QPB10?ORQ,1M#DRqPJPIPLPIP1PmPLP[10oSPZPGD<RoFHX9BPJPZPiPOPQPYDURi/JGRm,QLA3J1oX<JPAPJP}P}PmQ0:Q0DPAPA%fi%fkPGPGQ0EPiPkQ0FQ0?Q0@P6%2SRk16DO,5SRDPXPtPO10VORiP[DUPXP7POPVP[DU'?P@%2WRm%4[/6O,5YR}P\P4AV3;wQ0J7V<P^1Kjr/K21`A:R:'L9]A`Q0L/K0/L:9]A`5;_PFPdb5b7b8X0AX2AX;AX@AP1P<POP9P>DUP1Q0MP;P>C='?^0A^2A^;A^@AP1f@P[Q0APfO4b4W3W1P<P1O2n2001000000120000000b:D~Q0NG^G^PIPLPIPqPpI0pPSPQQ0?Q0@P6PkPD%2i?CitP@P\P4AVu<wRwP^P_1|_bPEP_Q0K,T`,x_PEP_Q06PEP_P_1K`rRr,_a1Trj,x_CICgFaPFPdb5b7b8X0AX2APR\T16;O,5<Q0810>ORT#2?CT=[[[^0A^2AP1Q0AP[PSP<P;O5b4X3}X1mP<P1O2n2001000000121000000b:O2E7Q0OP1Evb1PJPIPLAEIvl99IHPLPYQ0;?[O@PWPGD<DseQ0GPIPsPnPBPL1j1{X9B1jLs1RMePLPMP~PsPeQ0SE}Q0RQ0PQ0>Q0=Q0<PAP6%2V15V71RM<P?Q04Q0I,5Z1A|xQ0B/AK,pz,py;Y\P4PwP^P_P_P_1L]jR^,TaA;_`^CIP_P_1_^aQ0CCI5c_PEP_1|_PPEP_Ab_ajPEAb_]`CgFaPFPdb5b7b8X0AX2AX6U%8NP1PN%GNP;DNPR\g%2>1RM>[[[^0A^2A^6UP1P8PXP@P?PVP;O6b4W3W1P<P1O2n2001000000121000000bIb?b:CkPCQ0H-02LR;E7H0oE7PCP;E7A9Inl9EIsPIPsPnPlH0nE7WEP1O1n200110200021110111100bTb=PhQ09E7PJPIPLPIQ02Q079F?@PLP?A[hO<P@PGD<FHeW=XAAWLXBBP1H0lXBBXSAXNAo"). Qed.

(* [comment removed for export] *)
Definition popfree_spec (SEGS : list Segment) (p : Z) : Prop :=
  forall regs mem (i e c s n : Z),
    getr regs 10%bv = Z_to_bv 64 i -> getr regs 11%bv = Z_to_bv 64 e -> getr regs 12%bv = Z_to_bv 64 c ->
    getr regs 21%bv = Z_to_bv 64 s -> getr regs 19%bv = Z_to_bv 64 n ->
    (0 <= i < n)%Z -> (4 * n <= e < 2 ^ 64)%Z -> (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
    store_ok SEGS mem (Z_to_bv 64 (e - 4 * n)) (Z.to_nat (4 * (n - i))) = true ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 p) mem (seg_rom SEGS))
                  (mkst regs' (Z_to_bv 64 (p + 32)) (wbytes mem (Z_to_bv 64 (e - 4 * n)) (pf_bytes c s (Z.to_nat (n - i)))) (seg_rom SEGS))
      /\ getr regs' 10%bv = Z_to_bv 64 n /\ getr regs' 12%bv = Z_to_bv 64 (c + (n - i) * s)
      /\ getr regs' 14%bv = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15%bv = Z_to_bv 64 (e - 4 * n)
      /\ (forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).

Section PopFreeLoop.
Variable segs : list Segment.
Variable p : Z.                       (* [comment removed for export] *)
Hypothesis Hp : (28 <= p)%Z /\ (p + 32 < 2 ^ 64)%Z.
Hypothesis HF0 : fetch_word segs (Z_to_bv 64 p) = Some PW0.
Hypothesis HF1 : fetch_word segs (Z_to_bv 64 (p + 4)) = Some PW1.
Hypothesis HF2 : fetch_word segs (Z_to_bv 64 (p + 8)) = Some PW2.
Hypothesis HF3 : fetch_word segs (Z_to_bv 64 (p + 12)) = Some PW3.
Hypothesis HF4 : fetch_word segs (Z_to_bv 64 (p + 16)) = Some PW4.
Hypothesis HF5 : fetch_word segs (Z_to_bv 64 (p + 20)) = Some PW5.
Hypothesis HF6 : fetch_word segs (Z_to_bv 64 (p + 24)) = Some PW6.
Hypothesis HF7 : fetch_word segs (Z_to_bv 64 (p + 28)) = Some PW7.

(* [comment removed for export] *)
Definition iter_regs (regs : bvmap 5 word) (i e c s : Z) : bvmap 5 word :=
  regupd (regupd (regupd (regupd regs 14 (Z_to_bv 64 (c / 16))) 10 (Z_to_bv 64 (i + 1)))
                 15 (Z_to_bv 64 (e - 4 * (i + 1)))) 12 (Z_to_bv 64 (c + s)).

Ltac red_if :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?x else ?y] =>
      let v := eval vm_compute in (bv_eqb a b) in
      lazymatch v with
      | true => change (if bv_eqb a b then x else y) with x
      | false => change (if bv_eqb a b then x else y) with y
      end
  end.

Lemma u64_of_Z : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "h01xh12Hah24__x1h31zh41Hh52H0h62Hzh77__arithh84__ffh96__sat8h:6__sat9h;8__varmaph<5__with=1mh>1nh?1yp;1p;2p;3p;4p;<p;6p;7p;Bp;8p-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p710P1p8p10022p4p710P1p8g004Dj13Tg005lj16Tg01R7R1j25Tg00n:R2j20Tg00nVR3j24Tg005Nj1KTg01RTj2DTg008[j37Tg01S:R4j1;Tg00:Hj22Tg00o1j3>Tg00oWj1=Tg01SXj4`Tg00dcl<NTg0105j6MTg01T;j2LTg01Tcj3JTg00XEj1ITg00Xej1HTg00YEj2CTg00Ycj1ETg00ZAj1FTg00[Oj2BTg00Zlj29Tg01UGj3GTg00]8j48Tg015aj1ATg01DAj7@Tg00^Gj2?Tg00^ij2OTg00_Uj3PTg00`4j4QTg00`fj4RTg01Ujj1STg01VSj3TTg00m7j2_Tg01W?j2^Tg01Wij2]TP0j6WTg00Wij2XTg00d>l<YTg00cXlBZTg00]cj7[Tg01@Hj8\Tg00KER0f0R5'Xp=1g01XXR6g00<TR7P7P7P4P4f5R4f4R8f3R9f2R:f1R;P5M<Yp=VP7P7P7P7P7P7P1P5P;P:P1P9P8P4f6R1f7f8R<f9MBZp=UP;g00i\R=g00j;R>P>g00j[R?P5g00kbF[p=:P9P=P>P>P?P:P;P5G\p=<%15g00>ZR@#3RA#6RB%3A#3#3#3#3RA#6RC'5RD,05RE'4P7%KARA/D;A775:X37%1;RF%;ARG,5BRH,0;RI'410;DRJ,4FPFPIPFPJp-0/2F9>FFP7P7P2P5X07RJP210;5#=X?7X07P;P;127;PHPDPJPJPJP7P7g01Y615;5C`,27X=7X>7PBPB127BPGPCPJPJ%;5,27X06PAPC127CEVM:UM<NEM1LBC100B%1C100D[[%1BR6g01YZRJAJBC;UW1%1D\J^16P3%19109D%18108D'4P:%14101Dg00i0R1#I%H11C7;%E7%F7R1P71B7@R@g01G2197B=G7AC8,:1RB%A>R4P1P71970g01GYP@C8,:1R@P4P1P=P>P>P?P@PBF@C<C<1?1?P5P:g00@eR1g00AER?'21O5:=71?dAP70;CQb8b;b<X27%1:10:D'4\F\E^27P5P<P;P:O3b7W5W4P;P5O2n2001000000121000000b9b:CR%SA,0;,4Fe9TA;1_A;,^A1]A;EWW6X37o"). Qed.

Ltac gr := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].

Lemma pf_iter : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i + 1 <= n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + s < 2 ^ 64)%Z ->
  RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * (i + 1))) 4 = true ->
  exists regs',
    msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                (mkst regs' (Z_to_bv 64 (if (i + 1 <? n)%Z then p else p + 32))
                      (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom)
    /\ getr regs' 10 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 e /\ getr regs' 12 = Z_to_bv 64 (c + s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 (c / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * (i + 1))
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "p'0h01Hh13Hc0h21bi001bh34__x1h41zi011zh51rh67__arithh77__sat22h87__sat23h94__ffh:8__varmaph;5__with<2H0h=2H1h>2H2h?2H3h@7__sat24hA4__x2hB1qhC7__sat25hD7__sat26hE4__x3hF2e0hG2HahH1nhI3HlthJ2b1hK2b2hL5regs'hM3H10hN3H11hO3H12hP3H19hQ3H21hR2HchS3HcshT2HehU2HihV3HinhW3HnehX3HokhY3Hp0hZ3Hp1h[4Hr10h\4Hr12h]4Hr14h^4Hr15h_2Hsh`3V10ha3V12hb3V14hc4V15ahd4V15bhe4V15chf3Vsthg7__sat27hh7__sat28hi1ahj1chk1ehl1ihm3memhn4regsho3romhp1si021pp%0p%1p%2p%3p&0p&1p;1p;2p;4p;3p;8p;6p;5p;=p;>p;7p-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p710P1p8p101Z6p4p710P1p8p10022p4p710P1p8g004Dj1FTg004ij1DTg005Nj1lTg00OXj1_Tg01[=k219Tg0031k10VTg005lj1CTg00m7j23k10aTg00SOj24Tg00Wij2KTg00S2j2\Tg01R7k20;Tg00n:j2GTg00Q\k10<Tg01[ik40ITg00nVS00j2@Tg01\ij2ITg00Slj2=Tg01]Fj20Tg008[j32Tg0120j1:Tg01^8k20fTg01W?j29Tg01^Rk20PTg00:Hj2ETg01T;k20DTg01Tck30CTg00XEk10`Tg00Xek10_Tg015Ck118Tg00Yck116Tg00ZAk114Tg00Zlk20LTg00^Gk20{Tg00^ik20yTg00_Uk30vTg00`4k40rTg01_2k30pTg01:Zk207Tg00YEk20OTg01?Fk405Tg00[Ok204Tg01UGk30HTg015ak10TTg01_[k200Tg01`Oj2yTg01RTj2]k10gTg01a7k20STg00m]j2OTg010^j3VTg011Oj2QTg012Ij2<Tg012ij2TTg013Pj2STg0147j2RTg014]j2XTg01<7k20kTg01<`k30?Tg01aUk20iTg01bZj2wTg01cNk20FTg01dMj2ATg01eAk20RTg01eak30hTg01;Ck80QTg01Wik202Tg01fEk30eTg01fnj2uTg01gbk30dTg01Elk60cTg01hGk40bTg01i0k208Tg006Jk30BTg01icj5;Tg01jUj35Tg01kIj3}Tg01lEk30:Tg01m2m=0^Tg01mim=0]Tg01n`m=17Tg01oWm=15Tg020Nm=0\Tg021Dk209TP0j61Tg022Lk210Tg022kj4eTg023bm>0~Tg024bj3{Tg025]k20}Tg026Ok20ETg027Bk50zTg027fj56Tg028^m>0xTg019[k10wTg029Xk20WTg02:Tk20uTg02;Qj7jTg02<Mm>0qTg02=Gj4oTg02=bk40oTg00]8k40@Tg00]ck706Tg01BLk30UTg01C5k20YTg01Cak30ZTg00\Uk30JTg01DAk70nTg01@Hk80NTg02><k20mTg00\2k311Tg01EIk312Tg016ak60MTg02?=k60lTf1R0f0R1g00??S0140Bp=Wf3R2f2R3/00;21p=ag00KER4/K1p=>1\01,O3,32p=?g00@eR5g00AER6721p=Y209019{23p=Mf5R7f4R81323P0P1D;p>03f6R9P7P8P2P3P0D;;}1p=81401,33p=HA2978A2230/@1'@p=g1@01,@3p=vg00<TR:00L1p>0KP3g00i\S02g00j;R;P;g00j[R<P:P0g01GYP1H0@g00kbR=K06p=NP:P8P2P3P0P1E1p=cB0U:01p=fg00i0R>B0U:30g01HmR?+0Y<0Z1p=sB0J:01p=nP:P0g01G2P1H0@p=mP0Q02P;P;P<P1P=K06p>01P3Q02P;P;P<P0P1K0np>0GP2Q02P;P;P<P3P0P1L0Np=`P9Q02P;P;P<P7P8P2Q02P;P;P<P3P0P1L0NL0Np=bP:P7P8P2P320m01E1p=d1O01,33p=[A2:14p=L1\30/4192:2p=U1K431G01'@p=J1G301K14'@p=ZA2:01p=7B11:01p=x1G01,@3p>0j1\01,O3p=kB12:01p=|P3Q02P;P;P<P:P0g00k;R@P1H0@P=K06p>0>P2Q02P;P;P<P:P3P@B0J:01H0@P=K06p=q140192:3p=hP:P8P2P3P0P1J0Mp=if7R@1397P8P2P320F01E1p=tA2230/@1p=rA5823?501p=^20L:1:0J:0p=pP9A5782P3P0P1D;p>0A208019523p=PP9P7P8A{230P1D;p>13P:P3P0Q01P4P1J0Mp>0=20Y0?>0Z>1p>0|P0Q02P;P;g02?aS03P1P=K06p>0[P3Q02P;P;P0P1J0lp>0XP:P2P3Q01P0P1J0Mp=BP91378P2P3P0P1E1p>0tg02@AS049251p=~P9P7P8P2P320F01E1p>0s1@01,@3,@2,@8p=zg00>ZR=#FR?#DRA#lRB%F?RC#FS05#FRD#FRE#FRF#lRG#_RH+19S06Q05#l#_$0V\HS07Q07PHP@%FAS08#CS09,WBRI13G8RJCaPHf8%DA#CS0:,WBRAPJCaPHf9RK%D=RL#FS0;#FS0<#CRM,WBRNPJCaPHf:ROQ08#D#CS0=,WBRPPJCaPHf;S0>%DC#D#CS0?,WBRQPJCa%>K%C=RJ,4O/K9%CCRR/\@/KOQ0>%C?R@%CFRF+0;RS'GQ0>#>S0@Q0@f=S0Af<RT'4/GSp,4segsRUfBS0BPGf?S0CPRf@S0D/4JC?g00hQRV$0<S0E$0<RW$0<RX$0<RYH0I#Yp,2Hp%DLRZ#FR[#FS0F#CS0Gp,1pR\'KS0H%CES0I,4\S0J/GSS0K'@Q00Q0HQ0KQ06Q06PUp,2fxREfGS0L13G\S0MfFS0NfES0OPEP1PGP5P:fDS0P/4JR]Q0D'IP\Q0Jn0100000020000Q0NPGfCS0QPRP]C?R^PYQ0B%CDR_'=,3GR`CMQ0OJ03F8101IS0R13G]52HPH101AS0SQ0Q,3GPH101NS0TQ0BfAS0U5HGPH101PS0VQ0U,3GPH101QS0WQ0D,3GPH%C[S0X,WBR[,01S0YP`PH%DZRZ#CS0Z,WBR`,01S0[P^%_BR^A2^1I#:S0\A2^0N#:S0]A2^3[#:S0^A2^2`#:S0_1078S0`fLR]/0852H[[[[]5FgFgFg3vWL+0fP1Q0HQ0KQ0PQ0;#lRa1WaRS0a'9S0b-0P1,3GQ0O/=_,3GRb52HX4:Q0P20;@R'=13G1S0c=2HbX4:Q0P/=_,3GRb,EHQ0P00PRQ0P20D@FRc1G4@Rd%>F1G4S[[Re%>@Rfg01YZS0dB0C@F0UWGRFQ0d%>S[^GfRg&0`>Rh&0_>R>&18:S0e&16:Ri&14:Rj20L:4S0f&0KRRk3N20{j<RlP1P31E5620y13#YdB0v:40H0rR6b9b:b;%>RP1b6b7b880pRDcQ0P,3GRm,9GQ0PPcPePFPg207:XS0g207:WS0h207:VS0i'f;shP>P:P:Q0eP320O:3S0jH05P0Q0eH05S0kPiPj204:=R=Q0;-04:S0l'n&0K@S0m>0H:GS0n'm-01j&0T;RVPjQ0fQ0l5NjS0oPVPjQ0f=Nj=S0pPVQ0pQ0n,m=-01jS0q60GjS0rC`RWFbPlP6b9b:b;X3:XA:S0s1410/GS%>3RX%>2S0t1G2SS0u'@S0v\X[[^3:^A:S0wP1Q0NQ0LPKPOQ0>O5b6b7b8EdQ0b-00m=2HbeQ0a%_aS0xe,9a-00m=2HbQ0LQ0<#lRb%DZ#D#D#DS0y#D#D#D#D#C,WbS0z'yS0{,]G-0S1,3G1OSJRZfHS0|5[GRm52HX4:Q0L,OZROQ0c=2HmX4:13GORO,EHQ0L00SZQ0LQ0O?V_K%>_RKQ0N/=_#>[PcPePFPgQ0|/Q_%L_Rm#:RXfIRnP_1=n_Ro1<n_CU[1Tn_1G4_RpfJRq/<_Rr?Jr_[1Sq_1G_4RrfKRs/<_S0}Q0}5Z_[1Rs_1=]_S0~#L\m1X]_fMRt/<_S10/7t\m1=t_S11P:fNRu/<_S12P:207:YS13Q0g20k:RS14Q0h60?:S15Q14Q0i60?:S16'f'f;shS17P>P:P:20O:2P2Q0eH05P0Q0jH05S18PiPj204:CS19Q0n'm-01jS1:PVPj204:LS1;,xkQ195NjS1<PVPj&0KJS1=,n=S1>Q1;5NjS1?PVPWC`FbPlP6b9b:b;X3:XA:XE:1G3SS1@1\R3S1A/K2S1B143J/K2S1CQ0t%>8S1D@0j8SS1E[[[[^3:^A:^E:P1fQRWPufRRLQ0OQ0NQ0LQ0|O7b6b5bBb?b>b=b<b0b7b8b@RC+0iDcQ0L,3GRv,9GQ0LPCEdQ0{,wv=2HOeQ0z%_bS1Fe,yb,wv=2HOQ0|00FJQ0|,3G1WbJS1GQ1Fe,yb'AQ0|=HGJ52H1OZnRO1Wa@S1H,9aS1I-0R1,3G%DD#FS1J#CRD-0;@Rv/ORRC?kRqS1K,3GS1L52HX4:20;@@Rw,\OQ0cQ1L52HX4:g01XXS1M%_1S1N%_0S1OQ00%_3?20119231920'7Rx[S1P19301931'7%_2?230S1Q[S1R%_8?223\xB0h301S1SP1n2001000000120000000WKWJWHS1TQ1MQ1NQ1OQ1R]K]J]HS1UP1PG1OZq/\wS1V,3GS1WQ1LQ1V,]GAkCRsRx,3G,9GS1X,71X4:Q1K,]G1OZs/\w,]G/71X4:P:P:&0gGRyPyQ1VQ1KP:\:/EyQ0|?V_TS1Y%>o\KS1Z20D@@1G4w\f\dQ0dB0C@@0UXGfQ0d%>w[^GfPcPePFPg20D@DRo%>D1G4v[\dRdQ0dB0C@D0UXGfRDQ0d%>v[^GfRvfORT/Q_S1[fPRyP_1=y_S1\1<y_RzCU\XS1]1Ty_S1^1<W_S1_Q1_;J_\pS1`1SW_S1a1<L_S1bQ1b5Z_\rS1c1RL_S1dfSR{/=_S1e#L\mS1f1X{_S1gfTR|/<_R}/7|\mS1h1=|_S1iP:fUR~/<_S1jP:PhP>20O:0S1kPiQ0nQ1='|/|=S1lQ0m%l?60H:'xQ0mQ1J#l60H:/|kS1J1xk=S1m'|60>jPlP6b9b:b;X3:1OZ1/\wAkCR1'7^3:P1fYRwO1b6b5bBb?b>b=b<b0b7b8b@bCbDbgbhL0QQ1L,9GQ1K-02GDcQ1W,9GQ1V-02GDcO4b020RO@Q0LQ0>7V_S0>Q0|/=_#>\KS1VPcPePFPg1Qq_S1WPsP_1=s_S1KQ0}CU\XS0}1Ts_S1n1<]_S1oQ1o;J_\pS1o1S]_S1pQ10Q105Z_\rS101Rt_S1q1=u_S1r#L\mS1s1Xu_S1t1<T_S1u/7T\mS1v1=T_S1wP:PzP:PhP>Q0ePiQ0fQ0m5NjPlP6b9b:b;PfP1b6b5bBb?b>b=b<b0b7b8b@:0eO@Dc13GOR@,9GPOQ0>Q1VPcPePFPgQ1WQ0}Q1nQ1oQ1pQ10Q1qQ1sQ1tQ1vQ1wP:PzP:Q17P>Q18PiPjQ1:PVPjQ1<PVPjQ1?PVPjQ0pPVQ0fQ1l5NjQ1lQ0n'm-01j60GjFbFbPlP6b9b:b;X3:XA:XE:Q1@Q1BQ1CQ0t1OZ8RO?JOS[[[[^3:^A:^E:P1P{PyP|Q0LQ0|PnPqO7b6b5bBb?b>b=b<b0b7b8b@EdQ1I,u@PGPCPRPnC?RO52HeQ1HQ0xe,9a,u@=2HOPnQ1X9HG114sJ9kqRRO,3GR@52HX4:Q1TQ1UP1PGQ1X,4qS1U,3GS1TP@Q1U,]G14]J9ksRRa,3GS0x,9GRf,71X4:1]GxS1l14s1S1v,]G/7fX4:1]GOS1tAkCR]S1s,]G,4s,]G/71X4:14qxS1q/<S1<aSS10,71X4:Q0A9Vn_S1p1=q_#>\KS1oPcPePFPgPoPdPDPv1Qu_S1nPTP_Q1wQ1uCU\XS0}1TT_S1WAJzz_\pS1V1Sy_S0>Q1_Q1_5Z_\rS0m1RW_S1x1=L_S1y#L\mS1z1XL_S1{1<{_S1|/7{\mS1}Q1eP:P}P:PhP>P:Q0jP0Q0eH05S0jPiPj204:?R?Q1='n,xk,|=S1~Q0n,xk'nP=Q1J1xk?'|CqPlP6b9b:b;X3:XA:140JS1J9k1RS201\RSS21'41\R0S22,OC7h1^3:^A:P1fXR?fWRfO2S23b6b5bBb?b>b=b<b0b7b8b@bCbDQ21,4OQ1q'7Q21,4aS211<1S14tJS1q9k]RS24/<SS25'7X4:Q10Q25,71X4:Q10,E:Q21/<SB0daRSDcQ1s,4sP1Dib01<xS,4q/<SPqPxPSQ1pQ1oPcPePFPgPoPdPDPvQ1nQ0}Q1WQ1VQ0>Q0mQ1xQ1zQ1{Q1}Q1eP:P}P:PhP>Q0ePiPjQ02P;P;P<Q0nQ0f60>jJ0cPlP6b9b:b;%LSg01KBR<[P1b6b5bBb?b>b=b<b0b7b8b@bCbDH0bDcQ1l,4q,]GQ1t'7e19G@202GODcQ1X202GxDcQ1T,9GQ1U-02GDcO4b013GnS1U,9GS1TPnQ1YQ1ZPcPePFPgPoPdPDPv1Qt_PuP_Q1rQ12CU\X1Tu_Q1uQ1u;J_\p1ST_AZ_zz\r1Ry_1=W_S1u#L\m1XW_Q1b/7L\mQ1yP:Q1|P:Q0gQ15Q14Q0E-07:Rz60?:Q0i'f'f;shP>Q18PiPjQ0qPVPjQ19,xk=Nj=PVPjQ1;Q1='nS1=Q195NjPVPjQ0fQ1;5NjPVQ0rC`S0qC`FbPlP6b9b:b;X3:XA:XE:1G1S1\R2S15/K0142JS0E/K8Q1DQ1E[S1D[[[^3:^A:^E:P1P{PffVRxPqPsP]PtO7b6b5bBb?b>b=b<b0b7b8b@bCbDEdQ1UQ1L+08PGPnPR14qJC?52HRaePaPHPG14O4S1LQ0x92H1X2HP:PH&0aGRaPaQ1LPOPH\:/EaQ1pQ1oPcPePFPgPoPdPDPvQ1nQ0}Q1WQ1VQ0>Q0mQ1xQ1zQ1{Q1}Q1eP:P}P:PhP>Q0jPiQ1~Q0f'nQ1~60>jPlP6b9b:b;X3:XA:Q20/44Q20'7^3:^A:Q23b6b5bBb?b>b=b<b0b7b8b@bCbDL0Q1A@4POP4GtQ01:0Bb4S23Q1Fe,yb,A@=2H@Pq13GqS1F,9GS209HG1AHGsqR@52HX4:PnQ1v,3G=2H@X4:AHGqnRO,EHQ1TPnf>9Vq_S1TQ1K#>\KRaPcPePFPgPoPdPDPvQ1[Q1]Q1^Q1`Q1aQ1cQ1dQ1fQ1gQ1hQ1iP:Q1jP:Q0gQ0i,fzS0i;shP>Q0kPiPjQ0l/n=Q0n'm-01jPVPjQ0pPVPjQ0oPVQ0rC`FbPlP6b9b:b;X3:XA:1401/GS%>0Q0tQ0v[[[^3:^A:P1PfPxPnPqPsO5b6b5bBb?b>b=b<b0b7b8b@bCbDEdQ20PqQ1TPaPcPePFPgPoPdPDPvQ1[Q1]Q1^Q1`Q1aQ1cQ1dQ1fQ1gQ1hQ1iP:Q1jP:Q0sQ0wP1PxPfPnPqPsO5b6b5bBb?b>b=b<b0b7b8b@bCbDEdQ1FQ1U+08=2HOROePOQ06Q06PUPEPWQ0MPyPTPEP1P5P:14uJRO/IqP\Q0Jn0100000020000,3GS0wPyPGPtPRPOC?S0sPYQ0~,3GS1hCMS1gPTD;F8Q0R13GOS1f52HPHQ0S13GtS0SPHQ0TAHG]sS0TPHQ0V13GsS0VPHQ0WQ1FPHQ0YQ1hPHQ0[Q0sQ0\Q0]Q0^Q0_Q0`10x8S0[52H[[[[^5^FgFgFg3vWLQ1K,3GS1K95y[ROA[GZtS0`75`S0YQ1q,3GS0W75IS0RPGPCPRPtC?S1d75`S1cQ24,3GS2475`Ra?5N@RzPEPyQ0MPTPuD;S1aPEPzPGP5P:Q1q/InP\Q0Jn0100000020000PTQ24PYQ1KCMPuJ03S1q5}UPH10zIS1`Q0WPH10zAS1^13G]S1]PH10zNS1[P@PH10zPS1TQ1FPH10zQS20Q1UPH10z[S0vQ1KPH10z`S0rQ24Q0\Q0]Q0^Q0_Q1\,3GS0o95~[S0lA[GZLS0k75`S1v14LJS1~,3GS0j75IS1}PGPCPRPLC?S1{75`S1zPGPWPRQ1~C?S1x75`S0mAHGyTS0>75NS1V/08S1W10~8S0}52H[[[[^5^S1nCrFgFgFgPUQ1aPEP5Q06Q01:0BB4R4:0:B[Py10yNS01Q0b+0095y[n0100000020000Q0M/ARS1aPTPuD;Q1q&0VH&0TH'ES1oPEPUPyQ0MPTPug00=2P[PNQ0ap,3HF0Q04,E5S04g02@aN=0^PH14\RS0a,3GS1pPUPE10WNQ0b+0095W[P1PyPTPEQ1h95W[S1LA[GZuS0x75`RzPIQ1fP`PGPCPRPuC?D^P`Q0sPNQ0TD^S1EQ0wQ1gPTD;S1gF8X2HPHQ0VPUPEQ0b-00195W[Q1pPyPTQ1gF8X2HPHQ1KPUPEA5W[1Q1pPyPTQ1gF8X2HPUPEPOQ1pPTPuD;PEP5Q06B0:B`4S0wPO10OIQ0{'w95O`n0100000020000Q1p/ARS12PTPuD;Q1qQ1oPEPUPOQ1pPTPug00BQP`PIQ0zp,3HF1Q04g02A]N=0]PHPGQ0a/4RS0zPUPEQ1LQ1L/0IS1pQ0{'w75`P1PyPTQ1gF8X2HQ0C9Vs_Q0~#>\KPcPePFPgPoPdPDPv1Qy_PWP_Q1uQ1_CU\X1TW_Q1bQ1b;J_\p1SL_Q1|Q1|5Z_\r1R{_Q1i#L\m1X|_Q1j/7~\m1=~_S1_P:1<x_S0~P:PhP>Q1kPiPjQ05#CS05,p=S0C1n=kPkCqPlP6b9b:b;X3:Q05,41S1L141R;hR^3:P1P\O1S1qb6b5bBb?b>b=b<b0b7b8b@bCbDQ05,4\S05Q0z'7Q05PUPEQ11,3GS1Z95L[S1YQ1Y/0IS1XQ0{'w75`Q0cPWPyPEQ1YA[GZTS1t75`S1l14TJS0e,3GS1s75IS21P`PGPCPRPTC?P`PGPuPRQ0eC?S10D^PNAHGt]P5P:Q0e/IsP\Q0Jn0100000020000,3GPWQ10PYQ1ZCMPyK0AS10F8X4:PH10WIS0ePUPEQ1YQ0{,w175`Q05,3GS25PWPyQ10F8X2HS26PH13GuS27Q26PHQ0xPUPEQ1Y?5`1Q25PWPyQ10F8X2HPUPEPzQ25PyPTD;PEP5Q06B0:BI4Pz10zIQ1G,ybS0x'A95zIn0100000020001Q25/ARS26PyPTD;Q1gQ1oPEPUPzQ25PyPTg00D9PIPIQ1Gp,3HF2Q04g02BYN=17PHPGQ05/4RS1GPUPEQ1lQ1l/0IS25Q0x'A75IP1PWPyQ10F8X2HQ0D9V]_Q11#>\KPcPePFPgPoPdPDPv1QW_PLP_Q1yQ1bCU\X1TL_Q1|Q1|;J_\p1S{_AZ_}}\r1R|_Q1_#L\m1X~_Q0~/7x\m1=x_S1bP:1<f_S11P:PhP>Q1kPiPj1p=MS1lQ0CPkCqPlP6b9b:b;X3:141MS0CQ1L;hR^3:Q1qb6b5bBb?b>b=b<b0b7b8b@bCbD14\MS1LQ1G'7Q1LPUPEQ1r,3GS1g95{[S28A[GZyS2975`S2:Q2:/0IQ0x'A75IQ0cPLPWPEQ2:14yJS2;,3GS2<75IS2=PGPCPRPyC?S2>75`RzPGPTPRQ2;C?S2?75`PNAHGutP5P:Q2;/I]P\Q0Jn0100000020000,3GPLQ2?PYQ1gCMPWK0AS1gF8X4:PHQ1XPUPEQ2:Q0x,A175IQ1L,3GS2?PLPWQ1gF8X2HS2;PH10LIS2@Q2;PH13GTS2AQ2;PHQ1sPUPEQ2:?5I1Q2?PLPWQ1gF8X2HPUPEQ21Q2?PWPyD;PEP5Q06Q0wQ21Q21Q21/0`Q1I'u75`n0100000020001Q2?/ARS1sPWPyD;Q10Q1oPEPUQ21Q2?PWPyg00EaP`P`Q1Hp,3HF3Q04g02CUN=15PHPGQ1L/4RS1HPUPEQ2=Q2=/0`S2?Q1I'u75`P1PLPWQ1gF8X2HQ0U9Vt_Q1r#>\KPcPePFPgPoPdPDPv1QL_P{P_Q1eQ1|CU\X1T{_AJ}}_\p1S|_Q1jQ1j5Z_\r1R~_Q1b#L\m1Xx_Q11/7f\m1=f_S1|P:1<?_S1eP:PhP>Q1kPiPj1p=_S1rQ1lPkCqPlP6b9b:b;X3:141_S1lQ0C;hR^3:Q1qb6b5bBb?b>b=b<b0b7b8b@bCbD14\_S0CQ1H'7Q0CPUPEQ1w,3GS0U95|[S2=A[GZWS2175`S1014WJS2;,3GS2B75IS2CQ2C/0`Q1I'u75`Q0cP{PLPEQ2CPGPCPRPWC?S2D75`S2EPGPyPRQ2;C?S2F75`S2GPNAHGTuP5P:Q2;/ItP\Q0Jn0100000020000,3GP{Q2FPYQ0UCMPLK0AS2;F8X4:PHQ2:/0`S2HPUPEQ2CQ1I,u175`Q0C,3GS2IP{PLQ2;F8X2HS2JPHQ29Q2JPHQ2>PUPEQ2C?5`1Q2IP{PLQ2;F8X2HPUPEPzQ2IPLPWD;PEP5Q06Q0wPzPzP`10zA10z`CPn0100000020001Q2I/ARS0wPLPWD;Q1gQ1oPEPUPzQ2IPLPWg00H5P`PAP`p,3HF4Q04g02DQN=0\PHPGQ0C/4RS2IPUPEQ2EP`Q2E/0AS1gQ2E/0`S2>CPP1P{PLQ2;F8X2HQ0B9Vu_Q1w#>\KPcPePFPgPoPdPDPv1Q{_P|P_Q1iP}CU\X1T|_Q1jQ1j;J_\p1S~_Q0~Q0~5Z_\r1Rx_Q1|#L\m1Xf_Q1e/7?\m1=?_S1|P:1<w_S1wP:PhP>Q1kPiPjQ08#F#CR},p=S08Q1rPkCqPlP6b9b:b;X3:141}S1rQ1l;hR^3:Q1qb6b5bBb?b>b=b<b0b7b8b@bCbD14\}S1lQ2I'7Q1lPUPEQ1zP`Q1z/0AR}Q1z/0`CPQ0cP|P{PEQ1VPGP5P:Q1~/IuP\Q0Jn0100000020000P|Q1xPYQ0oCMS1~P{J03S1VF8X4:PHQ2DPUPEQ1zP`P}P1CPQ1l,3GR}P|P{Q1VF8X2HPHQ2C/0AS0BPUPEQ1zP`P1Q1{CPP}P|P{Q1VF8X2HRuPHQ10/0AS2JPuPHQ2=/0AS2KPuPH10|AS2LPuPH13GyS2MPuPHQ2FPUPEQ1z?5`1P}P|P{Q1VF8X2HPUPEQ2GP}P{PLD;PEQ2G1A}RS2NP{Q2G/0`RuQ23,ybS2O'AQ2G/0[-09YPLK13Q2;Q1oPEPUQ2GP}P{PLg00I]P`P[Q23p,3HF5Q04g02EMPHQ2FPUP|Q2O,A1S23PYH0I#YX2HPHQ2FPUP|P1PYH0I#YX2HQ0DQ2FQ2O'AP7E1PuQ2EP`Q2FA2^`4S2FQ1MQ1NQ1OQ00Q1PQ1RQ1Q19821983'7[Q1SP0n2001000000120000000WKWJWHRuQ1MQ1NQ1OQ1P]K]J]HR}P1PBP`P4P0O419B`S1M19B4S1N'7Q0ZP:p-0RbP1P<Q0dP<n011010003001000010000XF:S1O<0=1P<210<1Rzb0b1b0W1Q2F#:eS2FCeE1N>0~PHPGQ1l/4RS1PPUPEQ0mP1P|Q0m/0`S1SQ2O'APYQ0m/0[S1QCMP{Q1VF8X2HQ0Q9VT_Q1\#>\KPcPePFPgPoPdPDPv1Q|_P~P_Q1_Q1jCU\X1T~_Q0~Q0~;J_\p1Sx_Q11Q115Z_\r1Rf_Q1|#L\m1X?_Q1w/7w\m1=w_S1wP:fZS1|/<_S1jP:PhP>Q1kPiPjQ0<#F#CS0<,p=S1\Q08PkCqPlP6b9b:b;X3:Q0<,41S08Q1r;hR^3:Q1qb6b5bBb?b>b=b<b0b7b8b@bCbDQ0<,4\S0<Q1P'7Q0<PUPEQ1u,3GS1r95x[S0QA[GZ{S1R75`S0014{JS2E,3GS0D75IS2GPGPCPRP{C?S2;75`S2PPGPLPRQ2EC?S2Q75`S2RQ0cQ2R/0`Q2O'AQ2R/0[-09YS2S5{~P|PEQ2RAHGWyS2T75NS2UPGP5P:Q2E/ITS2EP\Q0Jn0100000020000Q2QQ1r-09YS2V5{~S2WP|J03S2XF8X4:PHQ1xPUPEQ2RQ0<,3GRTQ23Q2S5{~P|Q2XF8X2HPHQ1z/0[S2SPUPEQ2RPTP~Q2QQ2O'APYP1CMP|Q2XF8X2HS23PHQ1}/0[S2YQ23PHQ1v/0[S2ZQ23PHQ0l/0[S2[Q23PHQ0oQ23PHQ1xPUPEQ2RPTQ2V9{~1P|Q2XF8X2HPUPEQ0mPTQ1~P{D;PEP5Q06B0:BN4Q0mQ0mPNQ0m/0NQ0m/0PCPn01000000201011ATRS06Q1~P{D;Q1VQ1oPEPUQ0mPTQ1~P{g00KcPNPNPPp,3HF6Q04g02FIN=0\PHPGQ0</4RS1~PUPEQ2RPNQ2R/0NS1VQ2R/0PS2RCPP1Q2WP|Q2XF8X2HQ0P9Vy_Q1u#>\KPcPePFPgPoPdPDPv1Q~_PxP_Q1bQ0~CU\X1Tx_Q11Q11;J_\p1Sf_Q1eQ1e5Z_\r1R?_Q1w#L\m1Xw_Q1jQ1|'7\mQ1|/=_S1wP:f[S1e/<_S11P:PhP>Q1kPiPjQ0G,p=S0~Q1\PkCqPlP6b9b:b;X3:Q0G,41S1\Q08;hR^3:Q1qb6b5bBb?b>b=b<b0b7b8b@bCbDQ0G,4\S0GQ1~'7Q0GPUPEQ1y,3GS1y95f[P`A[GZ|PI14|JRT,3GD^P`PGPCPRP|C?P`PGP{PRPTC?S08D^S1uPNQ1u/0NQ1u/0PS2XCPQ0cPxQ08PYQ1yCMS1yP~PEQ1uPNAHGLWP5P:1ITyS08P\Q0Jn0100000020000,3GQ1yP~K0AS2WF8X4:PHQ2P/0NS2VPUPEQ1uPNP1Q2XCPQ0G,3GRTQ1yP~Q2WF8X2HS2XPHQ2G/0NS23Q2XPHQ00/0NS2\Q2XPHQ0Q/0NS2]Q2XPH10xNS2^Q2XPHQ2P/0PS2XPUPEQ1uPN10fNP1CPPTQ1yP~Q2WF8X2HS2_PHQ2G/0PS2`Q2_PHQ00/0PS2aQ2_PHQ0Q/0PS2bQ2_PH10xPS2cQ2_PH13GWS2_PUPEQ1uPNP110fPCPPTQ1yP~Q2WF8X2HPHQ2MPUPEQ1uPN13GLS2dP1CPPTQ1yP~Q2WF8X2HPHQ2TPUPEQ1u?5N1PTQ1yP~Q2WF8X2HQ2EP51E51Q08=251P514xJS08/IL=251PUPEQ1|P[Q1_,3GS2EP`A[GZfD^PI14fJS2W,3GS1yP`PGPCPRPfC?D^P`PGPxPRQ2WC?S1uPNAHG~|D^S2TPTPwQ1uPYQ2ECMS2EP?PEQ2TPGP5P:P0P\Q0Jn0100000020000Q2EP?J03F8]IP014~J/IWS1u#YPUPEQ1i,3GS1i95w[S2eA[GZxS2f75`S2gQ08,3GS2h75IS2iPGPCPRPxC?S2j75`S2kPGP~PRQ08C?S2l75`S2mAHG|{S2n75NR5PTP?Q2lPYQ1iCMS2oPfD;S2pPEP5Q0;#D#lS0;Q0;Q0y#F#F#D#F#F#C'WS0;'yS0y-0}TS2qQ2oPfD;PEP5Q0MQ2oPfD;Q1oPEPUP5PTQ2oPfg00MKS2rPIPQQ0;p,3HF7S2sQ04g02GES2tPHQ2m/0IS2uQ2T/0Q-0E1S2v#YX2HS2wPHQ2k/0IS2xQ2wPHQ2i/0IS2yQ2wPHQ2hQ2wPHQ2m/0QS2wQ1y00E1S1y#YX2HS2zPHQ2k/0QS2{Q2zPHQ2i/0QS2|Q2zPHQ2g/0QS2}Q2zPHQ2e/0QS2~Q2zPH10wQS30Q2zPHQ2dQ2zQ0813G{,9G,I1S2z#YX4:PLQ2W/I1S2W#YX4:P1Q2d,9GS31PLQ0|9V|_S0|Q1_#>\KS1_PcPePFPgPoPdPDPv1Qw_S32Q1|P_Q1wQ1jCU\XS1jQ1|/T_S1wQ11Q11;J_\pS11Q1e/S_S33f\Rp/<_RX=Z_X\rS341Rp_S35f]Rp/=_#L\mS361Xp_S37f^Rp/<_/7p\mRm1=p_RpP:f_S38/<_R_P:Q13Q0iQ0gQ0hQ16'f'fRr00|h3sP>Q18PiPjQ1=/m=-0[jPjQ02P;P;Q03I0zR;60XjPVPjQ1:PVPjQ1mQ195NjS1mPVQ0qC`FbPlP6b9b:b;X3:XA:XE:Q1J/I1#YQ0uQ1A/K8Q1D[[[^3:^A:^E:P1fbS1AfcS1JQ38Q0APxPfPwO7b6b5bBb?b>b=b<b0b7b8b@bCbDEdQ2h,9GS19Q08Q0|Q1_PcPePFPgPoPdPDPvQ32Q1jQ1wQ11Q33Q34Q35Q36Q37PmPpP:P_P:Q14Q1360?:?srhP>Q18PiPjQ1>Q1;'m-0[j>0Xj;PVPjQ1:PVPjQ1<PVPjQ0pPVQ0fQ1>5NjQ1>Q0n'm-01j60GjC`S1>C`FbPlP6b9b:b;X3:XA:XE:141J/I0#YQ0uQ15/K8Q0t148JR;?J;S[S0t[[[^3:^A:^E:P1Q1AQ38Q1JQ0APxPfPwO7b6b5bBb?b>b=b<b0b7b8b@bCbDEdQ2hQ2d+0ES0A#YeQ30PtE1Q2~PwP[Q1iPQA2^Q[R;PuP}P1PBPQP[P0O419BQRS19B[Rr'7Q0?P:PbP1P<g02HARXPbP1Q0dP<P<n011020003100001000000S1iP<n011010003001010210102XF:RKQ0XP1CBP<Pzb0b1b0W1%:;eS0uD6S15E1Q2}Q2eP`Q2fPQA2^Q`R;PuP}P1PBPQP`P0O4Q1M,7SQ0?P:PbP1P<PXPbP1PXPbP1PXPbP1P<Q0dP<n011020003100001000000S0dP<P<n011020003101021010200S2fP<P<n011020003101021010200P<n011010003001010210102XF:S2eQ0ZP1CBP<Pzb0b1b0W1%:;eS0nD6S0fE1Q2|Q2gPIQ2hPQA2^QIR;PuP}P1PBPQPIP0O419BIR{,7SQ0?PKQ09P1CBP<Pzb0b1b0W1%:;eS0pD6S1;E1Q2{Q2iP`Q2jPQQ0nD6S14E1Q2wQ2kP`Q2lPQQ0nD6S03E1105QS02Q2mPNQ2nPQA2^QNS39PuP}P1PBPQPNP0O419BNR;,7SQ0?PKPMP1CBP<Pzb0b1b0W1Q39#:eS39D6S0?E1Q2yQ2gPIQ2hA2^I4RSPuP}P1PBPIP4P0O4Q1N,7{Q09Q1O<0=1P<Pzb0b1b0W1%:SeS2gCeS3:E1Q2xQ2iP`Q2jPIA2^I`RSPuP}P1PBPIP`P0O4Q1M,7{Q09P:PbP1P<Q0dP<n011010003001010210102XF:S2jQ0ZP1CBP<Pzb0b1b0W1%:SeS2iD6S3;E1Q2uQ2kP`Q2lPIQ2iD6S2lE1105IS2kQ2mPNQ2nPIA2^INRSPuP}P1PBPIPNP0O417{;Q09P:PbP1P<PXPbP1P<Q1iP<n011020003101021010200P<n011010003001010210102XF:S2nPMP1CBP<Pzb0b1b0W1%:SeS2mD6S3<E1N>0xPHPGQ0GQ0y'4PEQ2TP1Q2EP?D;S3=PEQ2TQ0MQ2EP?D;S3>5}UX2HQ0|Q1_PcPePFPgPoPdPDPvQ32Q1jQ1wQ11Q33Q34Q35Q36Q37PmPpP:P_P:PhP>Q1kPiQ0~Q0F$0wRS'p:0>j=PlP6b9b:b;X3:Q1\=h1S^3:Q1qb6b5bBb?b>b=b<b0b7b8b@bCbDQ0G/4SS0F,7\P\PEQ1eP[Q1b,3GRSP`A[GZ?D^PI14?JRJ,3GP`PGPCPRP?C?D^P`PGPfPRPJC?RJPNAHGx~D^RCQ0cQ1|PJPYPSCMRSPwD;RYPEPCQ0MPSPwD;5}UX4:Q3>-0WUQ0FP1Dib0Q2qQ0GQ0y+0uK0tFjWIQ1u#~PUQ2pPEP51ATRRJQ2oPfD;PEP5Q0J,3GRZQ2oPfD;Q1oPEPUP5PTQ2oPfQ2rPIPQQ0;Q2sQ04Q2tPHQ2uQ2v#~X2HRTPHQ2xPTPHQ2yPTPHQ2hPTPHQ2wQ1y#~X2HRTPHQ2{PTPHQ2|PTPHQ2}PTPHQ2~PTPHQ30PTPHQ2dPTQ08Q2z#~X4:PLQ2W#~X4:P1Q31PLQ0|Q1_PcPePFPgPoPdPDPvQ32Q1jQ1wQ11Q33Q34Q35Q36Q37PmPpP:P_P:Q0hQ0iQ13Q0gQ16'f;sh3sP>Q18PiPjQ1:PVPjQ1mPVPjQ1==Nj=PVQ0qC`FbPlP6b9b:b;X3:XA:XE:Q1@Q22/K2Q0E/K3Q1D[[[^3:^A:^E:P1Q1AQ1JQ38PxPfP?PwO7b6b5bBb?b>b=b<b0b7b8b@bCbDEdQ19Q08Q0|Q1_PcPePFPgPoPdPDPvQ32Q1jQ1wQ11Q33Q34Q35Q36Q37PmPpP:P_P:Q17P>Q18PiPjQ1:PVPjQ1<PVPjQ1?PVQ1>C`FbPlP6b9b:b;X3:XA:XE:Q1@Q1BQ1CQ0t[[[^3:^A:^E:P1Q1AQ38Q1JPxPfP?PwO7b6b5bBb?b>b=b<b0b7b8b@bCbDEdQ0A#~eQ30PtE1Q2~Q15E1Q2}Q0fE1Q2|Q1;E1Q2{Q14E1Q2wQ03E1Q02Q0?E1Q2yQ3:E1Q2xQ3;E1Q2uQ2lE1Q2kQ3<E1N>0qPHPGQ0G/4RRGQ3=PEQ2TPZQ2EP?D;R?5}UX2HQ0|Q1_PcPePFPgPoPdPDPvQ32Q1jQ1wQ11Q33Q34Q35Q36Q37PmPpP:P_P:PhP>Q1kPiPjQ0I,p=Q0~PkCqPlP6b9b:b;X3:Q0I,41Q1\;hR^3:Q1qb6b5bBb?b>b=b<b0b7b8b@bCbDQ0J/7GQ0JPEPCPZPSPwD;9}UYX4:20WU?PGP1Dib0PJQ0GPRGtFjWIn0110001020101P1O1bIb2Q2_Q2M+08P9E1Q2cPsE1Q2^P]E1Q2bPxP[Q1rPPA2^P[R]PuP}P1PBPPP[P0O419BPRJ/7rQ0=PKQ0XP1CBP<Pzb0b1b0W1%:]eS2bD6E1Q2aQ0QP`Q1RPPA2^P`R]PuP}P1PBPPP`P0O4Q1M,7JQ0=P:PbP1P<Q2fP<n011010003001010210102XF:Q0ZP1CBP<Pzb0b1b0W1%:]eR]D6E1Q2`Q00PIQ0DPPA2^PIRGPuP}P1PBPPPIP0O417J{Q0=PKQ09P1CBP<Pzb0b1b0W1%:GeS2`D6E1Q2XQ2GP`Q2;PPP]D6E1Q2RQ2PP`Q2QPPP]D6E1Q2]PxP[Q1rPNA2^N[RGPuP}P1PBPNP[P0O417;rPMP:PbP1P<PXPbP1P<Q0dP<n011020003101021010200P<n011010003001010210102XF:R?Q0XP1CBP<Pzb0b1b0W1%:GeD6E1Q2\Q0QP`Q1RPNA2^N`RGPuP}P1PBPNP`P0O4Q1M,7;PMQ2jQ0ZP1CBP<Pzb0b1b0W1%:GeRGD6E1Q23Q00PIQ0DPNA2^NIRUPuP}P1PBPNPIP0O417;{PMP?Q09P1CBP<Pzb0b1b0W1%:UeD6E1Q2VQ2GP`Q2;PNPGD6E1Q1VQ2PP`Q2QPNPGD6E1Q1~P1Dib0Q06Q0<PRGtFjQ1xQ2O'AP9E1Q2[P~P[Q0oA2^[4RGPuP}P1PBP[P4P0O4Q1N,7rQ0XQ1O<0=1P<Pzb0b1b0W1%:GeRGCeE1Q2ZQ0lP`Q0kP[A2^[`RUPuP}P1PBP[P`P0O4Q1M,7rQ0XQ2jQ0ZP1CBP<Pzb0b1b0W1%:UeRUD6E1Q2YQ1vPIQ0jP[A2^[IR?PuP}P1PBP[PIP0O417r{Q0XP:PbP1P<PXPbP1P<PXPbP1Q1iP<P<n011020003101021010200P<n011020003101021010200P<n011010003001010210102XF:Q09P1CBP<Pzb0b1b0W1%:?eR?D6E1Q2SQ1}P`Q1{P[PUD6E1Q1QQ1zP`Q1xP[PUD6E1Q1SQ1zP`Q1xQ2FCeE1Q1PP1Dib0Q2NQ1lPRGtFjQ2MQ2D+08P9E1Q2LPsE1Q2KP|P[Q0UPAA2^A[R|PuP}P1PBPAP[P0O419BARs/7rQ0:PKQ0XP1CBP<Pzb0b1b0W1%:|eR|D6E1Q2JQ2=P`Q21PAA2^A`RYPuP}P1PBPAP`P0O4Q1M,7sQ0:Q2eQ0ZP1CBP<Pzb0b1b0W1%:YeRYD6E1Q0BQ10PIQ2BPAA2^AIRwPuP}P1PBPAPIP0O417s{Q0:PKQ09P1CBP<Pzb0b1b0W1%:weRwD6E1Q1gQ2CP`Q2DPAPYD6E1Q2>Q2CP`Q2DQ2FCeE1Q2IP1Dib0Q0wQ0CPRGtFjQ29Q1I'uP9E1Q2HQ28P`Q29Q2FCeE1Q2?Q2:PIQ2<P`A2^`IRSPuP}P1PBP`PIP0O4Q1M/7{Q0ZPKQ09P1CBP<Pzb0b1b0W1%:SeD6E1Q1HP1Dib0Q1sQ1LPRGtFjQ2AQ0x'AP9E1Q2@PqE1Q1XPLP[Q1ZPIA2^I[RLPuP}P1PBPIP[P0O417{rQ09P:PbP1P<PXPbP1P<Q2fP<n011020003101021010200P<n011010003001010210102XF:Q0XP1CBP<Pzb0b1b0W1%:LeRLD6E1Q25Q1YP`Q1tPIQ2iD6E1Q1GP1Dib0Q26Q05PRGtFjQ27Q0{'wP9E1Q0ePnE1Q1pPWP[Q1hPIPLD6E1Q0zP1Dib0Q12Q0aPRGtFjQ0VQ0b+00P9E1Q01Q0NE1Q1aP\PRK0sFjPHP@PHQ1E/0IQ1fPHQ1EPAQ0SCaRRQ0T92H1PHQ1E/0PQ0VPHQ1E/0QQ1FPHQ1E/0[Q1hPHQ1E/0`Q0sQ0\Q0]Q0^Q0_PHQ2UP8Q0[Ca[[[[^5^R\CrR9CrRLCrRnCrRb3vCrX2HPH10aIRXPHP1Q1fQ0TQ0T52HR{/@bRb,@RCrX2HRRPHQ1c/0IRqPRPHQ0R/0IRSPRPHQ0WPRPH10aARRQ1fQ1f52HRZQ0S92H1RC;vbX2HRbPHQ1c/0AREPbPHQ0R/0AR6PbPHQ0Y/0ARlPbPH10OARkPbPH10yAR=PbPH10aPRbPZPHPWPAQ0SCaRjP{Q0V92H1RiPnDzX2HRnPHQ1c/0PR>PnPHQ0R/0PRhPnPHQ0Y/0PR_PnPH10OPRpPnPH10yPRmPnPH10aQRnPZPjP{PHPWPPQ0VCaRvQ1F92H1RD/@LDzX2HRLPHQ1c/0QRdPLPHQ0R/0QRoPLPHQ0Y/0QRgPLPH10OQRFPLPH10yQRePLPH10a[RLPZPjP{PvPHPWPQQ1FCaRWQ1h92H1;v9DzX2HR9PHQ1c/0[RcP9PHQ0R/0[RtP9PHQ0Y/0[RfP9PH10O[RVP9PHQ1KP9PH10a`R9PZPjP{PvQ1hQ1h52HRjPHP1Q0sP\Cr5vWDzX2HRTPHQ24PTPHQ1]PZPCP{PvQ0sQ0s52H=vj\Rj,@WRWDzX2HPHQ1FPZQ0SQ0S52HR\P{PiPWDzX2HPHQ1UPZP\P{Q0VQ0V52H1@DjDzX2HQ0WQ0W52HQ1]Q1]52HRjA2H@@RDQ1FQ1F52HR{Q1UQ1U52HR\Q1KQ1K52HRZQ24Q2452HRWQ1n'@Ri'@Rv'@RC'@RT'@R5'@Q0W,EHPjP5Q1],EHPDPT1EH@P{PCQ1F,EHP\PvQ1U,EHPZPiQ1K,EHPWQ1nQ24,EHQ0\Q0]Q0^Q0_PHQ0m/08RW10x792H1X2HRxPHQ1z/08R7PxPHQ1}/08RiPxPHQ1v/08RZPxPHQ0l/08RvPxPHQ0}PxQ0},EHPvP~P[Q0oP8P0D6E1PZQ0lP`Q0kP8P1D6E1PiQ1vPIQ0jP8P2D6E1P7Q1}P`Q1{P8P1D6E1PWQ1zP`Q1xP8P1D6E1Q1WQ0mPNQ0>P8P3D6E1W^W]W\W[X5^CoCoCoCoCoCoCoPeQ0PE1PmQ0OE1P=Q0LE1P9Q1cP`Q24Q2FCeE1Q0rPaPNP@P`A2^`NR9PuP}P1PBP`PNP0O4Q1M/7;Q0ZPKPMP1CBP<Pzb0b1b0W1%:9eD6E1PVPyP[Q1KPGCeE1PfPOP`Q0`P[PUD6E1PtQ0YPIQ0WP[P?D6E1PcQ0RP`Q1dP[PUD6E1PLQ1cP`Q24P[PUD6E1Q0vPaPNP@P[A2^[NRUPuP}P1PBP[PNP0O417r;Q0XQ2nPMP1CBP<Pzb0b1b0W1%:UeD6E1PFPyP[Q1KPQQ0uD6E1PgPOP`Q0`PQQ0nD6E1PoQ0YPIQ0WPQQ0pD6E1PdQ0RP`Q1dPQQ0nD6E1PnQ1cP`Q24PQQ0nD6E1Q20PaPNP@PQQ39D6E1PpPyP[Q1KPPQ2bD6E1P_POP`Q0`PPP]D6E1PhQ0YPIQ0WPPQ2`D6E1P>Q0RP`Q1dPPP]D6E1PbQ1cP`Q24PPP]D6E1Q1TPaPNP@PPA2^PNR]PuP}P1PBPPPNP0O417J;Q0=PKPMP1CBP<Pzb0b1b0W1%:]eD6E1PkPyP[Q1KPAP|D6E1PlPOP`Q0`PAPYD6E1P6Q0YPIQ0WPAPwD6E1PEQ0RP`Q1dPAPYD6E1PRQ1cP`Q24PAPYD6E1Q1^PaPNP@PAA2^ANRYPuP}P1PBPAPNP0O417s;Q0:PKPMP1CBP<Pzb0b1b0W1%:YeD6E1PSQ0YPIQ0WQ2gCeE1PqQ0RP`Q1dPIQ2iD6E1PXQ1cP`Q24PIQ2iD6E1Q1`PaPNP@PIQ2mD6E1Q1[PaPNP@A2^N4R^PuP}P1PBPNP4P0O4Q1N,7;Q1O>0=M1P<Pzb0b1b0W1%:^eCeE1CoH0obabfbebdb`bcbbWZWYP0P1O2n2001000010121000000biWXWSW_WRWTWWWVWUWPWQWOWNWMXH:Xp:Xj:Xk:Xl:WoWmWno"). Qed.

Lemma pf_loop : forall k regs mem rom i e c s n,
  n = (i + Z.of_nat (S k))%Z ->
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + Z.of_nat (S k) * s < 2 ^ 64)%Z ->
  (forall j, (i <= j < n)%Z -> RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * (j + 1))) 4 = true) ->
  exists regs',
    msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                (mkst regs' (Z_to_bv 64 (p + 32)) (pf_mem mem e c s i (S k)) rom)
    /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
    /\ getr regs' 12 = Z_to_bv 64 (c + Z.of_nat (S k) * s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 ((c + Z.of_nat k * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "p'0h01rh15regs'h24__x1h34__x2h41Hh54__x3h62H0h77__arithh87__sat22h97__sat23h:1bi001bh;4__ffh<8__varmaph=5__with>3Hn0h?4cstrh@1zhA2H1hB2H2hC2H3hD2H4hE7__sat24hF1qhG1nhH3HcshI1xi011xhJ3H19hK3HmshL4Hms1hM3HnehN3HokhO3R19hP4__p1hQ1jhR2H5hS2H6hT2H7hU2H8hV2H9hW2HnhX1chY1ehZ2e0h[1ih\1kh]3memh^2q0h_2r0h`4regsha3romhb1shc3H10hd3H11he3H12hf3H21hg2Hahh2Hchi2Hehj2Hihk2Hshl3Hs1hm3R10hn3R11ho3R12hp3R14hq3R15hr3R21hs7Rothersht7__sat25hu2b0hv1mhw1Ahx1Bhy1Chz1Dh{2Hjh|3Hksh}4Hms2h~2IHi023S10i033S11i043S12i053S14i063S15i073S19i083S21i097Sothersi0:5regs1i0;5regs2i0<1yp%0p%1p%2p%3p%4p&0p&1p;1p;2p;3p;4p;6p;5p;Ep;;p;7p;8p;<p;Bp-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p710P1p8p101Z6p4p710P1p8p10022p4p710P1p8g004Dj1aTg004ij1mTg005Nk10TTg00OXk10PTg01[=k21DTg0031k11:Tg005lj1XTg00m7j23k110Tg01]Fj22Tg008[j30k11?Tg00S2R1j27Tg00Wij2STg01R7k212Tg00n:j2ATg00Q\R2j1>Tg00SOR3j24Tg01[ik40RTg02Hfj6GTg01icj55Tg00RRR4j19Tg0120k10;Tg01^8S00j2;Tg02Iek11ATg016ak60NTg01T;k21<Tg01Tck319Tg00XEk118Tg00Xek113Tg00YEk20WTg015Ck10{Tg00Yck10yTg00ZAk10wTg00[Ok20MTg00Zlk20VTg01UGk30sTg015ak10rTg00^Gk20qTg00:Hj2^Tg00^ik20pTg00_Uk30oTg00`4k40fTg019[k10nTg01:9k20mTg01:Zk20FTg01Ack30lTg01BLk30<Tg01C5k20ETg01Cak30DTg02JFmE0eTg01\ij2\Tg00SlS01j2:k10hTg02KFk20cTg02KhS02k30bTg010^k30Bk20}Tg011Oj2tTg012Ij2@Tg012ij2sTg013Pj2rTg00nVR5j26Tg0147j2qTg014]k202TP0m;0kj6PTg02=Gk409Tg02=bk40^Tg02LLk10jTg02Lmk11CTg016CR0j1ETg00gmR6k10OTg00oWk11>Tg00V]j4yTg00WDk106Tg02MNk41=Tg00\2k30=Tg021Dk20UTg024bk30YTg02N9k317Tg02O:k716Tg01kIk30?Tg02P<k611Tg00`fk40~Tg01;Ck80ITg00c7k40zTg006Jk30xTg00m]j2}Tg01?Fk414Tg00\Uk315Tg00]8k40>Tg00]ck70KTg01@Hk80LTg01DAk70vTg01?dk61;Tg01SXk40uTg00d>m<0]Tg00cXmB0gTg00dcm<0tTf0R7#>#9p>0@g00<TR8f2R9f1R:/4730p=Fg00??:0x:7p=vf3R;129:;07p=eg00KES03/S7p=<%9:/77p=c149:/A7p=U1S9:/67p=j1}:7,39p>0Sg00@eS04g00AER<707p>0Cf6R=f5R>f4R?179:,};'330/67p=8f7S0517;9,4?/::,3>70=/67p=HA0=>?A0;9:/67'6p=1149:,3;90>?/67p=YQ05P=P>P?P;P9D5<0?:/67p==14:7,39p=T179:,4;/:7,3?p=]12:790;9p=?A0;9:/67,6?,6>p=OQ05P>P?P;P9P:D580?=/67p=ZP?P;P9P:P7D5:0?=>p=_13:790;9p=D1::7,39p=B16:7,69,6;,6?p=VP8P9P:P7H14p=~B158:7p=RP8P:g01G2P7H0>p=|P:g00i\R@g00j;RAPAg00j[RBP7g00kbRCK0Kp>0GP;P@PAPAPBP9P:P7L0Lp=zP9P@PAPAPBP8P:g00k;RDP7H0>PCK0Kp>05P9P@PAPAPBP8P:g01GYREP7H0>PCK0Kp=kA08:7p=IP9P@PAPAPBP:P7K0vp>0Q17:7,}9,3;p=M20U:7:0Y;9p=w139:90?;/67p=`1:9:,3;90>?/67p=bA0;9:/67p=J17:7,}9p>04A0>?;16:7,69'6p>0d14:7,79p=n1}9:,3;90>?/67p=u14:7,79,};,3?p=fQ0517?;,}>,3=13:7-0U940Yp=dQ039087p=g1A:7,69p=xQ03,S7p={P8P:PDP7H0>p>0aP:P@PAPAPBP7J1;p>0`P?P@PAPAPBP;P@PAPAPBP9PCK0KP:P7L0Lp=p12;9=0?:/67p=Q16:7,69p>0_A0;9:/67,6?p=oP?P;1^9:P7H09p>0AP=P>P?P;P9P:P7H09H09p>0:P8P?P;P9P:P7EPp>08%>7#>p>1BP>P?P;P9P:%>7EGp>01%97#Ep=K17:7,49p=W%E:/77p>1@149:/47p>071^87p=CP8P8g01Y6P7H0up>0\g00eHS06Q06P8P8P2P4P4P;P6P9P:P7N<0]p>03Q06P8P8P8P4P4P>P?P;P9P:P7N<0]p=lP8P8P8P8P0P=P>P?P;P9P:P7N<0]p>00P8P8P8P8P8P8P3P7P:P9P3P;P?P>P=Q05f8S07f9S08NB0gp=hP8P8P7P:P9P;P?P>P=Q05Q07Q08N<0tp=iP8P:PEP7H0>p>0iP=P@PAPAPBP>P?P;P@PAPAPBP9P:P7L0LL0Lp>0JP>P?P;P9P:%>7#>EGp=N%E9/7:,4;,3?90=>/67p=LP>P?P;P9P:D5>0?=7p>0[%E:/77,49,3;p>0Z%9:/77,49,3;p>0H14;9%9:/77'4p=[149:/:7p>0XP8P8P8P8P8P8P1P7P:P9P1P;P?P>P=Q05Q07Q08NB0gp>0|Q06Q06g00>ZR1#aR@#mRE$0TR3%a@R0#aR4#aR6#aR2#aRC$0TRD$0PRF+1DRG&0T4$0P$1:\FS09Q09Q07$0@9F7?PFQ07%aER4#X,v3S0:13D>S0;CeS0<Q08%mE#X,v3S0='2S0>Q0;50FS0?PFf:S0@%m1RE#a#a#X,v3RHQ0;CeS0APFf;S0B%m4#X,v3R4Q0;CeS0Cf<S0D%m0#m#X,v3RI'2S0EQ0;50FS0FQ0@#<S0G%X0R0Q05'7Q0@'SS0HQ0B%X@RJ%XCRC+12RK'AS0IQ0B#<S0JQ0Jf=RLfCRM#>Q0D'c;UKfARN1A7L7j7p,4segsROfDRP%X1RQ,4:S0K,70S0L:0SDNg00hQRR#>RS#>S0M#>S0N#>S0OH0R$0C[^Q8S0PPOp,2fxRTfERUp,1pS0Q,3DRVPPPMPTP7Q0Q%X2'4S0R,3DR2PPPNf@RWf?S0SfBRXfFRY#>S0TEGPMD5PFQ0:,27RZf>S0U,3DR[PFQ0=,27R\13DNS0VPF127HR]PDPWQ0T#9S0WQ0S'7PF1274R^Q0S,3DR_PF127IR`P[PF%mES0X#a#X,v3R[,27RaPDPW%9YQ0S%X6R6PFQ0X#m#X,v3Rb,27RcPDPNP0Q0U&0P3R3Q0:9037$0;RdA03:H$0;ReA039[$0;RfA03;b$0;Rg12>?RhfJRi/2?S0Y50F[[[[]0F8GHF1EYF1G=X1G,;G[[[[[[[[[[[[[^G8^b8^X8^Y8^[8]a]]]`S0ZW\Q09Q09%9SRj9F7?Q0<Q0?Q0AQ0CQ0FQ0GQ0HQ0IQ0JQ0JQ0D,7j=ULKQ0PQ0UPOPTPYPVPUPPD5S0[PTP7P2PUPXPNPWPMPSEGPPA0FZ_S0\13DXRj90F\S0]PFP]ATDN:13DWRk90F^S0^A0F`_S0_PFPaPDPNQ03PWP6D]PFPcPDPXP0Q0SPFPhfKR_P?C?\g\f\e\d^03F8S0`EOEOGZX1G,;GX@8P8Q0U,7QS0aAUW7KX@8P:Q0UQ0U$1AS0bJ0NQ0SQ0U;UKP8Q03POPTfGRlPVPYPUD5RmPTP7P2PYPMPXPNPPPSEGPUF_RnA0FZkRo13DMRp90F\RqPFP]PD14XNCDRrQ0V90F^RsA0F`kRkPFPa14X:=BD6PFPcPDPMP0PWPFPhfLRtP?C?\g\f\e\d^03RuF8RvEODVX1G,;GX@8PWPnPoPqPrPsPkPFPaABD:6PvEODVX1G,;GX@821<JCS0cQ03/AJ%<CQ03/AK[[S0d%<JRvg01YZRoB19JC:UWgS0e%<K\o^gvS0fg00i0S0g$18S0hQ0g$13S0i20W89S0j&0{8S0k7~:S0l&0y8S0m&0w8Rv20M81Ro20M8@R@'RS0n20V8J>0s8DS0o'|-0GvS0p&0rAS0qQ0pCz20qvBS0rP7P9Q04/^<S0s20p79$0CdQ03>0o8:S0tH0fS0ub;b<b=X28X38147:S0v/AK14:9S0w/AK[^28^38P7PXPMP;O3b7b8b9Q0S=UWKPYPUPPPMPXPNPWQ0SPLQ0DQ0BQ0@Q08Q07Q0cQ0dQ0eQ0fQ0g&0n1-0m820F8SS0x60l820F8RS0y60<8S0zg01HmS0{+0EQ0h40DS0|Q0iQ0lQ0mPv20V8QS0},RoS0~:05v@RRQ0qQ0~=kv@S10CzQ0rQ0ub;b<b=X28X38147QS11,I:R1Q0K/S9[^28^38P7PXPYPNO3R<b7b8b9Q05P=P>P?P7P9PMQ0cQ0dQ0eQ0fQ0|Q0iQ0lQ0mPvPRQ0qAkvoo1|o@-0Gv60QvS12CzQ0rQ0ub;b<b=X28X381A:9S139j::\1^28^38P<b7b8b9O2NE0ePOPmPTP7Q04P814PQRm/\WQ0QQ0Rn0100000020000,3DPYPDPMP0PmCMR<Q0OABDX6R1CwPUPFPZPDPmPqPrPsPkPFPaP1PFPcP<PuF1DVD`GZX1G,;GQ00PGPOPTfHRuPVPlPYD5S14PTP7Q04P814UQR</\NQ0QQ0Rn0100000020000,3DPlPDPPP0P<CMR1Q0OABDM6RkCwPYPFPZPDP<13DPS1590F\S16PFP]PD14MXS17CDA0F^jS18Q0V90F`S19PFPaPkPFPcP1fMS1:/2?S1;90Fh\g\f\e\d^03S1<F1DVD`GZX1GPOPTfIR1PVPuPlPTP7P2PuPUPPPMPYPSEGPlD5PFPZPjPFP\13DUS1=PFP]PDPPPMPFP^PpPFP`PjPFPaPDPPP6PFPcPDPUP0PXfNS1>/2?S1?90Fh\g\f\e\d^03F8EbF1EYF1G=X1G,;GP7POPTPiPVP1PuPTP7Q04P814lQRj/\MQ0QQ0Rn0100000020000,3DP1PDPYP0PjCMRkQ0OABDU6R<CwPuD5PFPZPDPjPFP\13DYS1@PFP]ATDUPPFP^Q15PFP`PpPFPaP<PFPcPkPFPhfOS1AP?C?\g\f\e\d^03F1F1F1D`G=S1BP5POPTP_PVPiP1D5S1CPTP:Q04P814uQRk/\PQ0QQ0Rn0100000020000,3DS1DPiPDPlP0PkCMS1EQ0OABDY6S1FCwS1GP1F_PFQ0:,2:S1H13DkS1IPFQ0=,2:S1J13DlS1KPF12:HS1LATDYUS1MPF12:4S1NQ1=PF12:IS1OQ15PF12:[S1PQ1FPF12:bS1QQ1E12=?S1RfPS1S/2?S1T50F\g\f\e\d^03CJF1F1F1POPTQ1:PVPtP_D5S1UPTP7P2PtP1PuPlPiPSEGP_PFPZQ1@13D1S1V90F\S1WPFP]PD14ulCDS1XQ1K90F^S1YQ1@90F`S1ZABDu6Rk90FaS1[PFPcPDB0410YCDfRR</2?S1\90Fh\g\f\e\d^03S1]DVJ0dGZX1G,;GP7POQ1UPTP;Q04P814iQS1^/\YQ0QQ0Rn0100000020000,3DS1_PtPDP1P0Q1^CMS1`Q0OPkCwS1aP_F_PFQ0:,2?S1b14_QS1c,3DS1dPFQ0=,2?S1e13DiS1fPF12?HS1gATD1uS1hPF12?4S1i13DuS1jPF12?IS1kQ1KPF12?[S1lABD16S1mPF12?bS1nPDPiP0Q1cCMS1oQ08/2?S1pfSS1q/2?S1r50F\g\f\e\d^03CJF1F1F1P5PFQ0:,2>S1sPD14tQRkCDPFQ0=,2>S1t13D_S1uPF12>HS1vATDi1PF12>4S1wQ1VPF12>IS1xQ1jPF12>[S1yPDPiP6PF12>bS1zPDP_P0PkPFQ0@/2?S1{fTS1|P?C?\g\f\e\d^03F8EbF1F1POPTfQRkPVQ1SQ1APTP7P2Q1SQ1:PtP_Q1>PSEGQ1AD5PFPZQ1fPFP\Q1:,3DS1}PFP]ATDt_S1~PFP^Q1uPFP`Q1fPFPaABDt6S20PFPcPDQ1:P0PifVRp/2?S2190Fh\g\f\e\d^03F8F1F1F1G=X1G,;GP7Q05Q0:'2S22Q1>/4QS23,3DS2450FPFQ07Q0='2S25Q1>,3DS26PFQ07/2HS27Q1:=TDtS28PFQ07/24S2913DtS2:PFQ07/2IS2;Q1uPFQ07/2[S2<Q1:=BD6S2=PFQ07/2bS2>PDQ1>P0Q1A/4QS2?CMS2@12L?S2AfWS2B/2?S2C50F\g\f\e\d^03F1F1F1P5Q0>Q1A,3DS2D50FPFQ08/2HS2EPDQ1>Q1:PFQ08/24S2FQ1}PFQ08/2IS2GQ2:PFQ08/2[S2HPDQ1>P6PFQ08/2bS2IPDQ1AQ1S=n0QPFQ0U/2?S2JfXS2KP?C?\g\f\e\d^03EuEbF1EYPOPTfUS2LPVQ1|Q1qPTP7P2Q1|PkQ1SQ1AP<PSEGQ1qD5PFPZQ26PFP\13DkS2MPFP]Q1SQ1A5TDS2NPFP^Q2DPFP`Q26PFPaQ1S=BD6S2OPFPcPDPkP0Q1>fZS2P/2?S2Q90Fh\g\f\e\d^03F8F1F1F1G=X1G,;GP7Q0BQ0='2S2RQ2M50FPFQ0D/2HS2SQ1S9TDkS2TPFQ0D/24S2UQ1S,3DS2VPFQ0EQ2DPFQ0D/2[S2WABDk6S2XPFQ0D/2bS2YPDP<P0Q1qPQDfS2Z12N?S2[f[S2\/2?S2]50F\g\f\e\d^03CJF1F1P5PF12LHS2^PD14<kCDPF12L4S2_Q2MPF12LIS2`Q2VPF12L[S2aPDP<P6PF12LbS2bPDQ1qQ1|=n0Q12X?S2cf\S2d/2?S2e50F\g\f\e\d^03EuEbF1POPTfYS2fPVQ2KQ2BPTP7P2Q2KQ2LQ1|Q1qPpPSEGQ2BD5PFPZ13D<S2gPFP\Q2L,3DS2hPFP]Q1|Q1q5TDS2iPFP^Q1q,3DS2jPFP`Q2gPFPaQ1|=BD6S2kPFPcPDQ2LP0P<f^S2l/2?S2m90Fh\g\f\e\d^03F8F1F1F1G=X1G,;GP7Q0S/2HS2nQ2i50FPF12W4S2oQ1|,3DS2pPF12WIS2qQ2jPF12W[S2rQ2L=BD6S2sPF12WbS2tPDPpP0Q2BPQDfS2u12U?S2vf_S2w/2?S2x50F\g\f\e\d^03F1F1P512N4S2yQ2h50FPF12NIS2zQ2pPF12N[S2{ABDp6PF12NbS2|PDQ2BQ2K=n0Q12Y?S2}f`S2~/2?S3050F\g\f\e\d^03EuF1POPTf]S31PVQ2dQ2\PTP7P2Q2dQ2fQ2KQ2BQ2PPSEGQ2\D5PFPZ13DpS32PFP\Q2f,3DS33PFP]PDQ2KQ2BPFP^Q2B,3DS34PFP`Q32PFPaQ2K=BD6S35PFPcPDQ2fP0PpCMfbS36/2?S3790Fh\g\f\e\d^03F1F1EYF1G=X1G,;GP712M4S38Q3450FPF12PIS39Q34PF12P[S3:Q2f=BD6S3;PF12PbS3<PDQ2PP0Q2\PQDfS3=121?S3>fcS3?/2?S3@50F\g\f\e\d^03CJF1P512UIS3AQ2K,3DS3B50FPF12U[S3CPDQ2PP6PF12UbS3DPDQ2\Q2d=n0QQ0YfdRj/2?S3E50F\g\f\e\d^03EuEbPOPTfaS3FPVQ2~Q2wPTP7P2Q2~Q31Q2dQ2\Q2lPSEGQ2wD5PFPZQ2P,3DS3GPFP\Q31,3DS3HPFP]PDQ2dQ2\PFP^Q2\,3DS3IPFP`Q3GPFPaQ2d=BD6S3JPFPcPDQ31P0Q2PCMffS3K/2?S3L90Fh\g\f\e\d^03F1F1EYF1G=X1G,;GP712lIS3MQ3G50FPF12u[S3NQ31=BD6S3OPF12ubS3PPDQ2lP0Q2wPQDfS3QQ1;fgRs/2?S3R50F\g\f\e\d^03F1P5PF121[S3SPDQ2l/:6CDPF121bS3TPDQ2wQ2~=n0QQ1?fhS3U/2?S3V50F\g\f\e\d^03EuPOPTfeS3WPVPjQ3?PTP7P2PjQ3FQ2~Q2wQ36PSEGQ3?D5PFPZQ2l,3DS3XPFP\Q3F,3DS3YPFP]PDQ2~Q2wPFP^PDQ2wPFP`Q3XPFPaQ2~=BD6S3ZPFPcPDQ3FP0Q2lfjS3[/2?S3\90Fh\g\f\e\d^03F8F1D`EYF1G=X1G,;GP712_[S3]Q3Z50FPF12tbS3^PDQ36P0Q3?PQDfS3_12k?S3`fkS3a/2?S3b50F\g\f\e\d^03CJP5PFQ1:/2bS3cPDQ3?14jQ8040CDQ1\flRr/2?S3d50F\g\f\e\d^03POPTfiS3ePVQ3UPsPTP7P2Q3UQ3WPjQ3?Q3KPSEGPsD5PFPZQ36,3DS3fPFP\Q3W,3DRqPFP]PDPjQ3?PFP^PDQ3?PFP`Q3fPFPaABDj6PFPcPDQ3WP0Q36fnRm/2?S3g90Fh\g\f\e\d^03F8F1D`EYF1G=X1G,;GP7Q1A/2bS3hPDQ3WP0Q3KPQDfS3i50FQ2L/2?S3jfoRR/2?S3k50F\g\f\e\d^03PGPOPTPrPVQ3aQ3[D5S3lPTP7P2Q3aQ3UPsQ3KQ3ePSEGQ3[A0FZqS3mPFP\PDQ3UCDS3nPFP]Q3K9TDsPFP^PDQ3KCDS3oA0F`qS3pPFPaABDs6PFPcPDQ3UP0Q3WPFPhfqRqP?C?\g\f\e\d^03F8S3qEOEOGZX1GPkQ3U/4QRB00cj1ABj1SjB1\Bj40bQ3e/4QS3rQ3W'\Q04Q02Q3[/4QRBQ3K'AQ3K/SBPOPTPRPVPmfmRBD5S3sPTQ2LQ04P8P:Q0QQ0Rn0100000020000,3DS3tPmPDQ3aP014rQS3uQ0OPDQ3[/:6GdS3vPBF_POPTfpRAPVPRPmD5S3wPTPpP2PRPrQ3aQ3[PBPSEGPmPFQ0:,2pS3xQ3e,3DS3yPFQ0=,2pS3z13DrS3{PF12pHS3|Q3aQ3[5TDS3}PF12p4S3~Q3[,3DRJPF12pIS40Q3yPF12p[S41Q3a=BD6S42PF12pbS43PDPrP0Q3ePFQ2]fuRCP?C?\g\f\e\d^03F8F1F1F1S44GZS45]KP:Q3a/4QS46/AsS47POQ3sPTQ2LPVQ3vPBF_Q3aQ2w80B6%<6S481:r6S49#<[Q0cQ0dQ0eQ0f1tm6%g6Rn$0;S4:1:R6S4;,761@R65FR[1sR6Q03/A6S4<1@A6Rw#<?xw6[1rA6Q03,A6S4=1@q6Rw,A6%{w'6[1qq6frRw/:6S4>#g\n202w6fsRx/@6/Ix\n1:x6S4?P8ftRy/@6S4@P8p-0S4AQ0hQ0i20W8:S4BQ0j7~9Q0mPvPv20M8ES4CQ0}'RS4D/|@Q0qPvPvQ4D-0a@Q0q20`v?DpDpQ0rQ0ub;b<b=X28X38WPQ4AQ0K/A7149QS4E,I:P?[[^28^38]PP7POPTf{REPVfzRzfyR{PTQ3FP2PzfwR|fvR}PCfxR~PSEGP{D5PFQ3FQ0:13DyS4FPFQ3FQ0=13D|S4GPFQ3FPH14}CS4H,3DPFQ3FP413DCS4IPFQ3FPIQ4FPFQ3FP[13D9PFQ3FPbPDP|P0PyCMS4JQ3Lp+01AS4K/2?S4L50F\g\f\e\d^03DQDQDQDQDQDQDQG=P~PyQ0DPxO5b7b0bFbDbCbBbAb6b8b9bEWKW4P7O1Q46,SsS4MPOQ3sPTQ2LP2Q3vPBF_POQ3wPTPpP2PRPDPrP014BQS3wCMS3vQ0OQ42CwPmF_Q44P7PFQ3w,3DS44A0F7JS3sPFQ2BQ0=13DBS4NCePFQ2BPHQ3a9TDrS4OPFQ2BP4Q3a,3DRSPFQ2BPIPJPFQ2BP[Q49,3DS49PFQ2BPbPDPBP0Q3[CMS4PPFQ2eP}P?C?\g\f\e\d^03S4QDQS4RDQS4SDQS4TDQS4UDQS4V40_X:FPFQ3{14mQS3{,3D=0FJS4WPFP7Q4NQ4VDoX:FPFQ3}Q4WQ4NQ4N50FS3}PFP7Q4OQ4UEOX:FPFPJQ4WQ3}Q4OQ4O50FS4OA0F7SQ4TDVX:FPFQ3yQ4WQ3}Q4OA0FSSRSQ3sQ4S'6DVX:FPFQ42Q4WQ3}Q4OPSA0FJJRJPFP7Q49Q4RDoDVX:FPFQ3vQ4WQ3}Q4OPSPJPFQ49Q49PFP7Q4PQ4QCJDoDVX:FP8Q3wPFPqPI13D7Ce170:/Sm1A7;9jq7POPyQ0L:0SDqS4QQ0OH0R$0C[^Q8PFQ2PPI13D;Ce14wQS4P,S?PF14xQRJ,3DQ0;PF13DwS49Q49PFATDqARSPSPF13DAS4OQ4OPFQ0;Q0;PF1:q6S0;,3DRSPSPFPDPwP0PJCMPDPwP0P>Q3F/2?S3}12E?S4W50F\g\f\e\d^03F8F1F1F1]4]O]N]M]JXG8PFPAPIQ44CeQ3{,70/SB14AQS44,A79jA7POPxQ0L:0SDAQ0OH0R$0C[^Q8PFQ2fPIQ44,3DCe14qQS0LQ0L'SQ4P,3DRJ=0FJS3v13DqS4RQ4R50FS4214ARS4S,3DRS=0FSS3s13DRS3yQ3y50FS4TQ3vABDA6S4UQ4U50FS4VPDPqP0Q4PCMS4XQ4X50FS4YPFQ30PzP?C?\g\f\e\d^03S4Z'6S4['6S4\'6S4]'6S4^'6S4_'61^FJRJQ42Q4_Q4R,^FQ3sQ4^PFPSQ4TQ4]PFQ3yQ3vQ4\PJQ4VQ4[Q4U,^FQ4YQ4ZPFQ4XQ0@I0AK0:I0AI0AK0:W4WOWNWMWJQ3eQ3UQ3?Q3FQ2dQ0UP:N;0kQ43P=EPQ41Q0@EPQ40Q0UEPQ3~PXEPQ3|PYEPQ3zPiEPQ3xQ1>EPH09Q45eWKW4P7O1n200210000001021100011000Q1AO1bub:H0^WsWqP:P7O2n2001000010121000000W4WpP:P7O2n2001000010121000000W4WOP:P7O2n2011000010121000000W4WrP:P7O2n2011000010121000000W4WoP:P7O2n2011000010121000000W4WnP:P7O2n2011000010121000000W4WmP:P7O2n2011000010121000000W4WKP:P7O2n2011000010121000000W4X1GP:P7O2n2011000010121101000bZblQ03,4W&0jWI08Q03Q0S'7Q0S$1CEPbHQ0aQ0bI08WNWHWkWhWiWMWjWJWfWeWdWcWWXG8Xb8XX8XY8X[8WaW]X`GQ06Q0ZQ09Q09Q08#>$0@9F7?Q0<Q0?Q0AQ0CQ0FQ0GQ0HQ0IQ0JQ0J&1BPQ0D'c=ULKQ0PQ0W#ERJPOQ0[PTP7P2PUPXPNPWPM%>uRSJ01PPQ0\Q0]PFP]17:W9TDNQ0^Q0_PFPaPDPN%9SS0_PWP6D]Q0`EOEOGZX1G,;GX@8P8Q0T$0@S0`Q0U?FX7X@8Q0DPJQ0T$0OS0TJ0NAFLNJP8%>lRJ$0@177W=UNKX@8P9%KJRS&0OJJ0NQ0S,7S=UWK%KuRSPOQ14PTP7P2PlPPPMPXPU%>iS14J01PYPFPZQ0VQ16PFP]PD%E:=WMXCDQ18Q19PFPaPDPMP:PXP6D]PFPcPDPPP0PNQ1<F8EOJ0dGZX1G,;GX@8P8Q0_%E7S1</7N=UXKX@8P7PS&0OuS19J0N21@SW=UNK%91S18PN%>1S16#9S0V#ES0^,4PRS,IWQ18@07QQ9FWPS0]&1?8S0\P7XI8RJQ0\1I:7$1>Z0<8XI8S0[PWPW%CWPSQ11XI8RSPJPSQ18O1S0WO1S0bO1S0a,4PPJPJPJ14:7$0\#CXv8XG8S45PPPP%CPQ0^Q0aPJPJPSQ1<$0\#CXI8S1<Q0VQ0bPJPJQ06%97#CWIS0bQ16Q0WPSP1Q18Q18#CH03ElK00M:hM:iP9CyS0WQ0]&06iS16%9iS0V#<S0aQ0cQ0dQ0eQ0fQ0hQ0iQ4BQ0mPvQ03-0V8S03=kvoS0^Q0qQ0^CzQ0rQ0ub;b<b=X28S3x%<7S3z%<:S3|[^28S3~P7Q1>#9S40P;O2b7b8b9b?b>Q0WQ0]Q16Q0aQ0cQ0dQ0eQ0fQ3xQ3~P7PYQ0@O2b7b8b9b?b>H1=Q18/7N#<Q14#9S18#ES3~,4US3x,INQ0V@07QQ9FNUS0aQ0\PJQ0\Q0[PNPN%CNQ3xPSPJPSQ0VO1S3xO1S16O1S0],4UPJPJPJQ45PUPU%CUQ3~Q0]PJPJPSQ1<Q18Q16PJPJQ0bQ14Q3xPSPiQ0VQ0V#CH03ElK00M:hM:iP;CyQ0a&06_%9_S0a#<Q0cQ0dQ0eQ0fQ0gQ0N-0F8Q0M-0F8S0MQ0xQ0y60<860<8S0y60<8Q0{+0EQ0h40DQ0iQ0jQ0k20W8;S0x7~;7~:S0NQ0mPvPvQ03Q0X-0M8S0X>0=8@+0iQ0qPvPvQ0XQ0}'RQ0}'RS0V>0=8@,RoQ0o'|Q0qPvQ03=kv@S3xQ0qQ0pCzDpDpQ0rQ0ub;b<b=X28X38X58179:S0p#<14;QS14/4QS16/79=U:K%<;AU;?K[[[^28^38^58P7Q1A#9PlPuP>P=Q0BO6b7b8b9b?b>Q17/AKP1PuPlPYPUPPPMPXPWQ0SQ0UPLQ0DQ0B%>_S0B#9S0S#ES17,4YRW,IXQ0a@07QQ9FXYRPQ0\PJQ0\Q0[PXPX%CXPWPSPJPSQ0aO1S18O1S0]O1RW,4YPJPJPJQ45PYPY%CYQ17PWPJPJPSQ1<Q0SQ0]PJPJQ0bQ0BQ18PSP_Q0aQ0a#CH03ElK00M:hM:iP?CyS0aPP&06tS18%9t#<S0BQ0cQ0dQ0eQ0fQ0gQ0MQ0z60<8Q0{+0EQ0h40DS0MQ0iQ0NQ0mPvQ03Q0X5kvS0XQ0qPvQ0V,Ro:05v@S0zQ0qQ10K0JQ0rQ0ub;b<b=X28X38X58%<9S0]Q169F9:S16Q4E/S;[[^28^38^58P7Q1S#9PlP_P;P?O5RWb7b8b9b?b>Q0@Q08Q07Q05P7P>PYQ0aPPQ18Q0BQ0cQ0dQ0eQ0fQ0MQ0iQ0NQ0mPvQ0XQ0qPvQ0zQ0qQ12K0JQ0rQ0ub;b<b=X28X38X58Q0]Q161A9;S129j99[[^28^38^58PWb7b8b9b?b>O2NE0eQ1BX1G,;GQ00PGPOQ1CPTP7Q1DQ1GP1PFPZQ1IPFP\Q1KPFP]Q1MPFP^Q1=PFP`Q15PFPaQ1FPFPcQ1EQ1T90Fh\g\f\e\d^03CJF1F1F1GZX1GPOPTPtPVP_PiPTP7P2P_PuPlPYP1Q1>ENPiD5PFPZQ1=PFP\Q1jPFP]PDPlQ40#ERWPYPFP^Q1@PFP`Q1=PFPaPDPlPWPYP6PFPcPDPuP0PUQ3`90Fh\g\f\e\d^03F8GHF1FLF1G=X1G,;GP7POQ1UPTP7Q1_Q1aP_PFPZPDQ1^Q1WQ1XQ1YQ1ZQ1[PFPcQ1`Q1]DoDVD`GZP5POPTQ1>PVQ1:PtPTP:Q04P8Q1c/\lQ0QQ0Rn0100000020000,3DQ1:Q1oQ0OQ1mCwPtD5K0[PFQ1HQ1dPFQ1JQ1fPFQ1LQ1hPFQ1NQ1jPFQ1OQ1KPFQ1PQ1mPFQ1QQ1oQ1RQ1r50F\g\f\e\d^03CJF1F1F1POPTQ1SPVQ1AQ1>D5RlPTP7P2Q1APtP_PiQ1:P<ENQ1>PFPZQ1VPFP\Q2:PFP]PDP_%K<RuPiPFP^Q1fPFP`Q1VPFPaPDP_PuPiP6PFPcPDPtP0P1Q3j90Fh\g\f\e\d^03F8GHF1FLF1GZX1G,;GP7POPlPTP;Q04P8Q1:/4QRl/\1Q0QQ0Rn0100000020000,3DQ1APDPtP0PlQ0OPD1:_6GdQ1>F_PFQ1bQ24PFQ1eQ1}PFQ1gQ1~PFQ1iQ1uPFQ1kQ1fPFQ1lQ20PFQ1nPDQ1:P0Q23Q1pQ2150F\g\f\e\d^03F8F1F1F1P5PFQ1sPDQ2?CDPFQ1tQ26PFQ1vQ28PFQ1wQ2:PFQ1xQ1uPFQ1yQ2=PFQ1zQ2@Q1{Q2C50F\g\f\e\d^03F1F1F1POPTQ1|PVQ1qP<PTP7P2Q1qQ1SQ1AQ1>PkPpENP<D5PFPZQ1}PFP\Q2VPFP]PDQ1A%KpR_Q1>PFP^Q26PFP`Q1}PFPaPDQ1AP_Q1>P6PFPcPDQ1SP0Q1:PFPhQ2fP?C?\g\f\e\d^03F8GHF1FLF1G=X1G,;GP7PFQ22PD14kQCDPFQ25Q2MPFQ27Q2NPFQ29Q2DPFQ2;Q26PFQ2<Q2OPFQ2>PDPkP0P<PQDfQ2AQ2Q50F\g\f\e\d^03F1F1F1P5Q0>Q2g50FPFQ2EQ2TPFQ2FQ2VPFQ2GQ2DPFQ2HQ2XPFQ2IQ2ZQ2JQ2]50F\g\f\e\d^03CJF1F1POPTQ2KPVQ2BPpPTP7P2Q2BQ1|Q1qP<Q2LQ2PENPpD5PFPZQ2MPFP\Q2pPFP]PDQ1qQ2P#KR_P<PFP^Q2gPFP`Q2MPFPaPDQ1qP_P<P6PFPcPDQ1|P0PkPFPhQ31P?C?\g\f\e\d^03S1qF8GHF1FLF1G=X1G,;GP7Q2RQ2p50FPFQ2SQ2iPFQ2UQ2jPFQ0EQ2gPFQ2WQ2kPFQ2YPDQ2LAn0pQQ2[Q2m50F\g\f\e\d^03EuF1F1P5PFQ2^PDQ2LQ1|'4CDPFQ2_Q2pPFQ2`Q2jPFQ2aQ2sPFQ2bQ2uQ2cQ2x50F\g\f\e\d^03F1F1POPTQ2dPVQ2\Q2PPTP7P2Q2\Q2KQ2BPpQ2fQ2lENQ2PD5PFPZQ2hPFP\Q3BPFP]PDQ2BQ2l#KR_PpPFP^Q32PFP`Q2hPFPaPDQ2BP_PpP6PFPcPDQ2KP0Q2LQ3}90Fh\g\f\e\d^03F8GHF1FLF1G=X1G,;GP7PFQ2nPDQ2B/4pCDPFQ2oQ34PFQ2qQ32PFQ2rQ35PFQ2tPDQ2fP0Q2PPQDfQ2vQ3750F\g\f\e\d^03F1F1P5Q2yQ3B50FPFQ2zQ34PFQ2{Q3;PFQ2|Q3=Q2}Q3@50F\g\f\e\d^03CJF1POPTQ2~PVQ2wQ2lPTP7P2Q2wQ2dQ2\Q2PQ31Q36ENQ2lD5PFPZQ33PFP\Q2d,3DPFP]PDQ2\Q36#KR_Q2PPFP^Q3GPFP`Q33PFPaPDQ2\P_Q2PP6PFPcPDQ2dP0Q2fPFPhQ3WP?C?\g\f\e\d^03F8GHF1FLF1G=X1G,;GP7Q38Q3G50FPFQ39Q3GPFQ3:Q3JPFQ3<PDQ31Q2l=n0QQ3>Q3L50F\g\f\e\d^03EuF1P5Q3AQ3I50FPFQ3CQ3OPFQ3DQ3QQ0YQ3R50F\g\f\e\d^03F1POPTPjPVQ3?Q36PTP7P2Q3?Q2~Q2wQ2lQ3FQ3KENQ36D5PFPZQ3HPFP\Q2~,3DPFP]PDQ2wQ3K#KR_Q2lPFP^Q3XPFP`Q3HPFPaPDQ2wP_Q2lP6PFPcPDQ2~P0Q31PFPhQ3eP?C?\g\f\e\d^03F8GHF1FLF1G=X1G,;GP7Q3MQ3H50FPFQ3NQ3ZPFQ3PPDQ3FP0Q36PQDfQ1;Q3\50F\g\f\e\d^03F1P5PFQ3SPDQ3F/:6CDPFQ3TQ3_Q1?Q3b50F\g\f\e\d^03CJPOPTQ3UPVPsQ3KPTP7P2PsPjQ3?Q36Q3WQ3[ENQ3KD5PFPZQ3YPFP\13DjPFP]PDQ3?Q3[#KR_Q36PFP^Q3fPFP`Q3YPFPaPDQ3?P_Q36P6PFPcPDPjP0Q3FPFPhPBP?C?\g\f\e\d^03F8GHF1FLF1G=X1G,;GP7PFQ3]PDQ3?/:6CDPFQ3^Q3iQ3`Q3g50F\g\f\e\d^03CJP5PFQ3cPDQ3K14sQ8040CDQ1\Q3k50F\g\f\e\d^03POQ3lPTP7P2Q3aQ3UPsQ3KQ3ePmENQ3[Q3mQ3nPFP]PDPs%KmR_Q3KH0ZQ3oQ3pPFPaPDPsP_Q3KP6D]Q3qEOEOGZX1G,;GP7PFQ3hPDQ3UQ3r8040CDPFQ3jPwP?C?\g\f\e\d^03Q4600csQ47Q4MQ46/\s40bQ3uQ3U'\Q04Q02Q3wQ3e'AQ3eQ3w'SPOPTPwPVPqPAD5S3wPTQ2LQ3tPqPDPmP014RQQ0OPD1:B6GdS3tPAF_POPTPyPVPxPwPTP7P2PxPAPRPmPq%>}S02J01PwD5Q4N90FZS04Q4O90F\S3uPFP]PDPR%9}S3U#ERsPmH0Z13DmS4M90F^S47Q4N90F`S4NPFPaPDPRPsPmP6D]PFPcPDB04A0BCDS46PFPhP{P?C?\g\f\e\d^03'6EOEOG=X1G,;G]LP:Q3{Q3['APOQ3wPTQ2LPVQ3tPAF_PyPpPwPDPRP0Q44Q0OPD1:m6GdPqQ44PR14mBPBPr%9CS44#ES3rQ0L=FB7X@8%>CS3q#9S3p#ES3o,4AS3n,IrS3mQ44/4QRp/4QRs,4AR_,IrS3aQ0\PJQ0\Q0[PrPr%CrS3lQ3nP_PJPJPJQ45PAPA%CAS3gQ3oPsPJPJPSQ1<Q3pPpPJPJQ0bQ3qPpPSPCQ44Q44#CH03S3iElK00M:hM:iQ2lCyS36Q3a&06}S3YQ3U#<S3fB0BA6jS3WQ48Q0;#<[S0;Q0cQ0dQ0eQ0f1tx6S3_Q4:1:y6,76Q4@5Fy[S4@1sy6S3\Q4<1@C6Rp#<?xp6[S3Z1rC6S3HQ4=1@}6Rp,A6%{p'6[S3X1q}6S3Q1:|6#g\nS3O202|6S3I1@~6Rs/I~\nR_1:~6RlP81@{6RtP8Q0|Q0iQ0jQ0x7~:S0jQ0mPvPvQ4DQ0}'RS0|,R@-0aoQ0qQ0},R@S0}Q4D'R:05voDpQ0rP7P9Q0sQ0tH0fRub;b<b=X28X38X58Q4E/4QS0t9F7:Q4EQ145F:[^28^38^58P7p+01CRW#9S0sf}RPP{Q0DO4b7b0bFbDbCbBbAb6b8b9bEb?b>Q3p&0OCS0DI08Q1>PiPYPXQ0UQ36Q3aQ3YQ3fQ3WQ0;Q0cQ0dQ0eQ0fQ3_Q4@Q3\Q3ZQ3HQ3XQ3QQ3OQ3IP_PlP8PtP8Q0hQ0iQ4BQ0mPvQ0^Q0qQ03Q0~5kvCzQ0rPub;b<b=X28Q3zQ0K#<[^28P7PPPwO2b7b0bFbDbCbBbAb6b8b9bEb?b>PjQ3?Q36Q3aQ3YQ3fQ3WQ0;Q0cQ0dQ0eQ0fQ3_Q4@Q3\Q3ZQ3HQ3XQ3QQ3OQ3IP_PlP8PtP8Q0gQ0yQ0{+0EQ0h40DQ0iQ0lQ0mPvQ3xQ0qPvQ0^Q0qQ03Q0n5kvK0JQ0rPub;b<b=X28X38Q3|Q3|149;#<[[^28^38P7PzPEPmPRO4b7b0bFbDbCbBbAb6b8b9bEb?b>Q3FQ3r14RmRj177m;UKX@8Q36Q3aQ3YQ3fQ3WQ0;Q0cQ0dQ0eQ0fQ3_Q4@Q3\Q3ZQ3HQ3XQ3QQ3OQ3IP_PlP8PtP8Q0hQ0iQ0jQ0mPvPvQ0|>0=8@,RoS0|Q0o'|Q0qQ0nQ4D>0=8@S4D'RS3IQ0o'|-0GvDpQ0rPub;b<b=X28X38X58Q0t=W7:S0t/AKQ0wQ14/79;UK[^28^38^58P7Q0sPzPEQ3eO4b7b0bFbDbCbBbAb6b8b9bEb?b>Q3pQ0DI08Q0L1A7B7j7POQ0OPyQ4XQ0OQ4U+0URB60YyRKQ4QQ4X:17ByQ3FP:%>|RB#9Ru#ERt,4wRl,Im%9|R_@07QQ9FmwS3FQ0\PJQ0\Q0[PmPm%CmPlPSPJPSP_O1RlO1RYO1Ri,4wPJPJPJQ45PwPw%CwPtPiPJPJPSQ1<PuPYPJPJQ0bPBPlPSP|P_%C_H03ElK00M:hM:iQ2~CyQ3F&06~%9~Rl#<Q3K:0Bw6Q48Q4?#<[Q0cQ0dQ0eQ0f1tC6Q4:1:}6,76=F}p[1s}6Q4<1@|6Rp#<?xp6[1r|6Q4=1A6s%{s'6[1q~61:{6#g\n202{61@z6/Iz\n1:z6P81@E6S3KP8Q0hQ0iQ0jQ0mPvQ10Q4C,|@-0GvRs60QvQ0qAkvo@>0QvsCzQ0rQ0ub;b<b=X28X38X58Q11Q137j:Q129j:9[^28^38^58P7PEQ0Up+01@RsPLO4b7b0bFbDbCbBbAb6b8b9bEb?b>O2K16W{XQ8OEPOPTQ2BPVPxPDPAP0Q0LQ0OPDQ4;GdRpPwPTP7P2PpPAPjPmQ0LQ02EGPwD5Q04Q3uPFP]PDPjQ02PmH0HQ47Q4NPFPaPDPjQ3UPmP6D]Q46Q2e90Fh\g\f\e\d^03'6EOEOG=X1G,;GQ00PGPOPTQ2KPVPKPxPTP7P2PKPqQ4SPRQ4PPBEGPxD5PFPZQ4MPFP\Q4RPFP]PDQ4S17uRPFP^Q3yPFP`Q4MPFPaPDQ4SP_PRP6PFPcPDPqP0PmQ1qF8GHF1EYF1G=X1GPOPTP}PVPCPyPTP7P2PCPwPqPAPxP~ENPyD5PFPZQ3yPFP\Q49PFP]PDPq%ElRlPAPFP^Q4OPFP`Q3yPFPaPDPqPlPAP6PFPcPDPwP0PRQ4W90Fh\g\f\e\d^03F8GHF1FLF1G=X1G,;GP7POPTQ2PPVP}PDPxP014yQRRQ0OPDQ4>GdRlPCPTP7P2PlPx14wqRlPqPR%>{RREGPCD5PFPZQ4OPFP\13DxRmPFP]PDPl1cRqPFP^Q4RPFP`Q4OPFPaPDPl%9{PqP6PFPcPDPxP0PAQ2x90Fh\g\f\e\d^03F8GHF1EYF1G=P5POPTQ2\PVP|PDPyP014CQRlQ0OPDQ4?GdRRP}PTP:P2PRPy14xwRRPwPl%>zRlEGP}D5K0[PFQ1HQ4RPFQ1JQ4FPFQ1LPDPR1clwPFQ1NQ49PFQ1OQ4RPFQ1PPDPR%9zS1PPwP6PFQ1QPDPyP0PqQ1RQ3050F\g\f\e\d^03F8GHF1EYF1POPTPzPVP{P~PTP7P2P{P}PCPyP|f|Rq#>RRJ01P~D5PFPZPmPFP\13D}RlPFP]PDPC%KqR_PyPFP^Q4FPFP`PmPFPaPDAWC_yS30P6PFPcPDP}P0Px12s?S1R90Fh\g\f\e\d^03F8EbF1FLF1G=X1G,;GP7POPTQ31PVP{PDP}P014|QR_Q0OPD1:C6GdRmP~PTP;P2PmP}14CyPyP_PREGP~D5K0[PFQ1bQ4FPFQ1eQ4GPFQ1gPDQ4H%>P/cCPFQ1iQ4IPFQ1kQ4FPFQ1lPDQ4H%9PS4HPCP6PFQ1nQ4JQ1pQ3@50F\g\f\e\d^03CJGHF1EYF1P5Q1sQ4I50FPFQ1t13D~RRPFQ1vPD14|}R_f~Rm#>P}H0HPFQ1wPlPFQ1xQ4IPFQ1yPDP_%9mS1yP}P6PFQ1zPDP~P0PCQ1{Q3E50F\g\f\e\d^03F8GHF1F1POPTPmPVPPPqPTP7P2PPPzP{P~PEQ4KENPqD5PFPZQ4GPFP\13DzR_PFP]PDP{Q4K#KRlP~PFP^PRPFP`Q4GPFPaPDAW{l~S3EP6PFPcPDPzP0P|PFPhp+01DS1{P?C?\g\f\e\d^03F8EbF1FLF1G=X1G,;GP7Q22Q4G50FPFQ2513DERlPFQ27PD14z{Rup+01BRB#>P{H0HPFQ2913D{RKPFQ2;PRPFQ2<PDPu%9BP{P6PFQ2>PDPEP0P~Q2AQ3R50F\g\f\e\d^03F8GHF1F1P5Q0>13DqRu50FPFQ2EPD14EzRR%>W/czPFQ2FP_PFQ2GPKPFQ2HPDPRQ0sPzP6PFQ2IPDPqP0P{Q2JQ3V50F\g\f\e\d^03F8GHF1EYPOPTPWPVPBQ4KPTP7P2PBPmPPPqPsp+01ER{ENQ4KD5PFPZPlPFP\13DmRRPFP]PDPP%K{RKPqPFP^PuPFP`PlPFPaPDPPPKPqP6PFPcPDPmP0PEPFPhp+01HS3VP?C?\g\f\e\d^03F8GHF1FLF1G=X1G,;GP7Q2R=0FRPFQ2SPD14mPRKp+01FRl#>/cPPFQ2U13DPR_PFQ0EPuPFQ2WPDPK%9lPPP6PFQ2YPDPsP0PqQ2[Q3b50F\g\f\e\d^03F8GHF1EYP5PFQ2^PD14smRKp+01GRu$0@;WmCDPFQ2_PRPFQ2`P_PFQ2aPDPK%9uPmP6PFQ2bPDQ4KP0PPQ2cQ3d50F\g\f\e\d^03F8GHF1POPTPuPVPlP{PTP7P2PlPWPBQ4KQ1{p+01IRK#>R_J01P{D5PFPZ13DsRRPFP\13DWS3dPFP]PDPB%KKRjQ4KPFP^Q4K,3DRpPFP`PRPFPaPDPBPjQ4KP6PFPcPDPWP0PsPFPhp+01LS2cP?C?\g\f\e\d^03F8GHF1FLF1G=X1G,;GP7PFQ2nPDPBQ4KP_Q4KC[CDPFQ2o13DBS2oPFQ2qPpPFQ2rPDp+01JRp#9S2r/7B:07WBP6PFQ2tPDQ1{P0Q4KQ2vQ3k50F\g\f\e\d^03F8EbF1P5Q2yQ3d50FPFQ2zQ2oPFQ2{Q1{p+01KR_#9S2{/7W807W=BD6PFQ2|PDP{P0PBCMS2|PFQ2}PAP?C?\g\f\e\d^03CJF1POPTP_PVPpPKPTP7P2PpPuPlP{Q3Vp+01MRBENPKD5PFPZQ1{,3DRjPFP\13DuPFP]PDPl%KBRRP{PFP^13D{S2}PFP`PjPFPaPDPlPRP{P6PFPcPDPuP0Q1{PFPhp+01PS2zP?C?\g\f\e\d^03F8GHF1FLF1G=X1G,;GP7Q38Q2}50FPFQ39Q2}PFQ3:PuPlp+01NS3:PlC[=BD6PFQ3<PDQ3VP0P{PFQ3>PxP?C?\g\f\e\d^03F8F1P5PFQ3APDPlCDPFQ3CPDQ3VPup+01OS3CPuC[P6PFQ3DPDPKP0PlPFQ0YPyP?C?\g\f\e\d^03F8EbPOPTQ3CPVQ3:PBPTP7P2Q3:P_PpPKQ2cp+01QRRENPBD5PFPZQ3V,3DRjPFP\13D_PFP]PDPp%KRRYPKPFP^PDPKPFP`PjPFPaPDPpPYPKP6D]PFPcPDP_P0Q3VPFPhp+01TRYP?C?\g\f\e\d^03F8F1D`FLF1G=X1G,;GP7Q3M=0FjPFQ3NPDP_Ppp+01RRjPpC[P6PFQ3PPDQ2cP0PKPFQ1;P|P?C?\g\f\e\d^03F8EbP5PFQ3SPDQ2c/4_p+01SRi/c_<0X6CDPFQ3TPDPBP0PpPFQ1?P~P?C?\g\f\e\d^03F8POPTPiPVPjPRPTP7P2PjQ3CQ3:PBQ2zp+01URtENPRD5PFPZQ2c,3DS1?PFP\Q3C,3DPFP]PDQ3:%9tS3T#ES3SPBPFP^PDPBPFP`Q1?PFPaPDQ3:Q3SPBP6D]PFPcPDQ3CP0Q2cPFPhp+01XS2cP?C?\g\f\e\d^03F8F1D`FLF1G=X1G,;GP7PFQ3]PDQ3:/4BQ3T/7B<0X6CDPFQ3^PDQ2zP0PBQ3`Q4W50F\g\f\e\d^03F8P5PFQ3cPDQ3::04R0CDPFQ1\PqP?C?\g\f\e\d^03POPTp+01WS1\PVp+01VR5PtPTP7P2P5PiPjPRPYp+01YS3cENPtD5PFPZQ2z,3DS4WPFP\13DiRBPFP]PDPjQ3c#KS3`PRPFP^PDPRPFP`Q4WPFPaPDPjQ3`PRP6D]PFPcPDPiP0Q2zCMRRPFPhp+01\S2zP?C?\g\f\e\d^03CJF1D`FLF1G=X1G,;GP7Q3h=0FRQ3jQ1R50F\g\f\e\d^03PGPOPTp+01ZS1RPVQ3cQ2cPTP7P2Q3cP5PtPYQ1\Q2z#>S3jJ01Q2cD5PFPZPBPFP\13D5S3hPFP]PDPtQ2z#9S3`#ERRPYH0ZS4WPFP^13DYS3^PFP`PBPFPaPDPtPRPYP6D]S3TPFPcPDP5P0PiCMS3]p+01_S3C/2?S3S90Fh\g\f\e\d^03CJF1F1F1G=X1GPkPTQ3cPVQ2cQ1\D5S1?PTPkP2Q2cPtPYPiP5p+01[S1;#>S3PJ01Q1\D5S3N60?OPFQ0:,2kS0:13DjRRPFQ0=,2kS3M13DtS0YPF12kHS3DQ1;#9S3A#ES3>#E=WYiS3<,3DS39PF12k4S38PBPF12kIS2yPRPF12k[S3kQ3>=WYiS3>/:6S2v,3DS2tPF12kbS2qPDPtP0PjCMRkPFQ21p+01^S2nP?C?\g\f\e\d^03S2bCJF1F1F1POQ1?PTPEPVQ2cPDPtP0145QQ0OPD1:Y6GdQ1\D5Q3NQ2LQ1:J11PFPRA0F7BS1:PFP<Q0=Q3hCePFP<PHQ4WPFP<P4Q3^PFP<PIPBPFP<P[Q3TPFP<PbQ3]Q2CQ3S50F\g\f\e\d^03S3SDQS2CDQRbDQS0=DQR<DQR[40_X:FPFQ0YA0FBBRIPFP7Q3hP[DoX:FPF14YiR[Q3P#9R4/7iS3N'4RH,3DS0OPIQ3hQ3h50FR0PFP7Q4WP<EOX:FPFPBPIP0PD14tYS3hQ3jPYH0HQ4W50FRtQ3^90F7Q0=DVX:FPFPRPIP0PtQ3^Q3^50FR<Q1:/6bDVX:FPFQ3A=W[iRb/:6S1:,3DS3^PIP0PtP<PIPFP7Q3TQ2CDoDVX:FPFPkPIP0PtP<PIPFPDQ3hQ3`PYP6D]Q3TPFP7Q3]Q3SCJDoDVX:FA0FRRR<Q0YQ0Y50FS3SQ0OQ3950FS0OQ3^Q2t50FS3^A0FkkS2tQ2b'6S39'6S3],6<S3T,6IRt'6R0'61^FRS3hQ3SP0Q0Y,^FQ0OPtP8PF&10DRtPtPHQ3<PF\8/^tS0OQ3<,IHQ3A/4QR0/7iS0Y,4[RR140QRQ=WYiRY'IQ0\PJQ0\Q0[PHPRPJPJPJQ45P[P[%C[Q3NQ0YPJPJPJ17:7$0\#CXv8XG8P4P0PJPJQ0bQ3PP0PSQ1;Q3AQ3A#CH03R0ElPiPi%CiN:0|M:hQ3<PY%CYM:i%E4RY,45Ri,IjAFj5QRQQ0\PJQ0\Q0[PjPj%CjPiPSPJPSQ3AO1RiO1RjO1R[,45PJPJPJQ45P5P5%C5PYP[PJPJPSQ1<P4PjPJPJQ0bQ3PPiP0ElK00M:hM:iQ1{CyS3PPQQ2z$06S3AQ3`#<S3`B0B56pS3<Q48Q1\/:6#<[S0YQ1\P5Q2nP5C[R500}6S1\%<5Q48Q3cQ2c'4p+01`R5Q2c'c<0X6#<[[S48Q0cQ0dQ0eQ0fQ1RQ3cp+01aRpQ3cC[/t6S3cQ4:Q1;Q1Rp+01bR0Q1RC[Ri1:i6,761@i63F[S1R1si6S2cQ4<Q2zQ1;p+01cRiQ1;C[Rj/@6R4#<?x46[S1;1rj6S3NQ4=p+01]RjQ2zp+01dR4Q2zC[R[/@6RY,A6%{Y'6[S2z1q[6S3SQ2nPjp+01eR[PjC[Rj/:6#g\nS2C202j6S0=Q3CQ2np+01fRjQ2nC[RY/@6/IY\nS2n1:Y6S4WP8P5Q3Cp+01gR5Q3CC[/@6S3jP81tp6S1?Q4:1:06,761@065F0[S2a1s06S2`Q4<1@i6R0#<?x06[S2_1ri6RiQ4=1@46R0,A6%{0'6[R01q46R41:[6#g\nRp202[6R[1@j6/Ij\nRY1:j6RjP81@56R5P8Q0hQ0iQ0jQ0mQ3IQ0|605vQ0rQ0ub;b<b=X28X38X58Q0vQ4E/7:RR'4Q0t'I^28^38^58P7p+020#9p+01hp+01iO3RHb7b_b^bVbUbTbSbRb0bFbDbCbBbAb6b8b9bEbtb?b>H0~L0IPIQ3T1^FBP<Q3]Q3hQ3^Q39P8PFPtPtQ1:Q2vQ0OP8P8&0hbQ3>$0hP6P6P8P8\8RtQ01Q01PbQ3>Pt\8Q01'^Q3PPQQ3AQ3`Q3<Q0YQ1\Q48Q0cQ0dQ0eQ0fQ3cQ1RQ2cQ1;Q3NQ2zQ3SQ2CQ0=Q2nQ4WP8Q3jP8Q1?Q2aQ2`Q2_PiP0P4PpP[PYPjP8P5P8Q0hQ0iQ0jQ0mQ0nQ4C>0=8@'RQ4D,Ro605vQ0rQ0ub;b<b=X28X38X58Q0vQ0p'4?F7R^28^38^58PHb7b_b^bVbUbTbSbRb0bFbDbCbBbAb6b8b9bEbtb?b>L0I%C6L0IL0IQ2tQ2bPFPkPFQ4LPFP7Q3CP>C?X:FQ2wP?P;P9P:P7O5Q21P>P?P;P9P:P7O5EPXzgXyfXxeXwdX03I0AK0:K0:K0:Q2qP:EPQ3kP>EPQ2yQ08EPQ38PLEPQ3DPNEPQ3MPUEPQ0:P1EPH09H0^Y09Y06P:P7O2n2001000010121000000W6Y05P:P7O2n2001000010121000000W6Y07P:P7O2n2011000010121000000W6Y08P:P7O2n2011000010121000000W6Y04P:P7O2n2011000010121000000W6Y03P:P7O2n2011000010121000000W6Y02P:P7O2n2011000010121000000W6W}P:P7O2n2011000010121000000W6Z0;GP:P7O2n2011000010121101000bZWLW4P7O1Q3[Q3{'SPOQ3wPTQ2LP2Q3tPAF_Q3mQ3aQ0\PJQ0\Q0[PrPrQ3lQ3nPSPJPSQ44O1RrO1R1O1RN,4APJPJPJQ45PAPAQ3gQ3oPNPJPJPSQ1<Q3pP1PJPJQ0bQ3qPrQ3iElK00M:hM:iQ2lCyQ3aQ3YQ3fQ3WQ0;Q0cQ0dQ0eQ0fQ1P#E=Wxw/t6Q4:%KE=WyxRy1:y6,761@y63F[1sy6Q4<Q30/@6Ry#<?xy6[Q30/r6Q4=Q4H#E=W}CRC/@6Ry,A6%{y'6[1qC6Q1y#E=W|}R}/:6#g\n202}6%Ks=W~|R~/@6/I~\n1:~6P8Q3E/@6P81tz6Q4:1:E6,76Q3K5FE[1sE6Q4<1@q6RE#<?xE6[1rq6Q4=1@P6Rq,A6%{q'6[1qP61:m6#g\n202m61@s6/Is\n1:s6P8Q4K/@6P8Q4AQ0MQ0iQ4BQ0kQ0x7~97~;Q0mPvQ0XQ0qPvQ4CQ0V,R@605vQ0qPvPvQ4CQ0}+0iQ0q20`v>DpK0JQ0rQ0ub;b<b=X28X38X58WPQ4AQ0]Q16Q4E,S;P=[[[^28^38^58]PP7POPTPKPVQ3VPuPTP7P2Q3VP{Q1{PWPlP_ENPuD5PFPZQ2oPFP\Q2}PFP]PDQ1{Q2{#EPWPFP^Q3dPFP`Q2oPFPaPDQ0@PFPcQ2|PFPhQ3:P?C?\g\f\e\d^03CJD`F1FLF1G=X1G,;GQ2rQ4KP{PXPMPUO7b7b_b^bVbUbTbSbRb0bFbDbCbBbAb6b8b9bEb?b>WLW4P7O1n200210000001021100011000Q1AO1bub:WsWqP:P7O2n2001000010121000000W4WpP:P7O2n2001000010121000000W4WOP:P7O2n2011000010121000000W4WrP:P7O2n2011000010121000000W4WoP:P7O2n2011000010121000000W4WnP:P7O2n2011000010121000000W4WmP:P7O2n2011000010121000000W4WLP:P7O2n2011000010121000000W4Z0:GP:P7O2n2011000010121101000bZblb|bHQ0_Q19I08bHbWQ0`Q0TI08WNWHWkWhWiWMWjWJWfWeWdWcWWXG8Xb8XX8XY8X[8WaW]X`GW~W\P7H0zW\o"). Qed.


(* [comment removed for export] *)
Lemma pf_wbytes_inside : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs))%Z ->
  wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "p'0h04__x1h14__x2h21ah31mi001mh41xh56__sat8h66__sat9h73Hx0h87__arithh94__ffh:8__varmaph;5__with<4__x3h=4cstrh>4Hnw0h?2Hxh@4__p1hA1zhB3HnwhC2IHhD1ni011nhE1HhF3HeqhG1bi021bhH5cstr0hI1yhJ2HahK4__p2hL4__p3hM4__x4hN2b1hO2b2hP2bshQ1ohR2H8hS2H9hT3HnehU3Hu1hV7__sat10hW7__sat11hX2b'hY4resthZ5rest'h[1si031sh\2z8h]2z9i041ei051lp%0p&0p;1p;2p;4p;6p;3p;8p;<p;5p;Bp;7p-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p710P1p8p101Z6p4p710P1p8p10022p4p710P1p8g004Dj1\Tg005Nk106Tg00OXj1STg00XeR1j1xTg0031k10^Tg01W?j22Tg00Q<j27Tg00RRR2j11Tg005lj1pTg01R7k20ETg00WiR3j28Tg00SOR4j20Tg00m7k20XTg00XEk104Tg00n:R5j26Tg00nVR6j2DTg00oWj1WTg01SXk40ITg00:Hj2VTg0105j6fTg00V]j4NTg00WDj1`Tg01T;k20@Tg01Tck30>Tg00YEj2jTg015Ck10;Tg00Yck108Tg00ZAk107Tg00[Oj2dTg00Zlj2vTg015ak10WTg00^Gk20VTg00^ik20UTg008[j3;j1yTg00_Uk30STg00`4k40RTg01Caj3?Tg017=k20QTg0120j1sTg017]R7k20OTg01lEj3HTg0089j2>Tg006Jk30NTg02Q<j3LTg01eak30MTg00Q\R8j13Tg018=R9j1aTg018]j4ZTg02Qak201TP0j6Fk80BTg024bj4rTg01UGk30GTg00`fj4|Tg01:Zj2~Tg02RZj2{Tg02SNk60DTg00m]j2BTg02TOk10CTg004ij1zTg00U]k20ATg00V@k30?Tg00dcl<oTg0199j2wTg01AIj2nTg019[k10=Tg01:9k20FTg01Acj3}Tg01EIk305Tg016ak60KTg02U1k50LTg00d>l<kTg00cXmB0:Tg01?Fk409Tg00\Uk30PTg00]8j4lTg00]cj7bTg01DAj7tTg01?dk60TTg01@Hj8uTg01BLk30]Tg01C5k20\Tg01Elk60[Tg01@lk20ZTg01Dek70YTf2R0f1R:'0f0R;'8p=916:;,D0p=E1B:;#ap=Mf4R<f3R=P0P:P;CZ'>p=<f5R>P<P=P0P:Cr;;;p=Ag00<TR?/V;p=4g00eHR@P?P?P?P2P2P=P0P:g00hQRAg00KERBP;M<kp>0HP?P?P?P?P?P?P4P;P:P0P4P=P<P>f6R4f7RCf8RDf9RENB0:p=QP?P?P5PCP5P4P>P<P=P0P:P;M<op=h18B;p=G16B;p=UP?P0P:P;H09p=@B0P?:;p=:P?P:g01G2P;Clp=TP:g00i\R5g00j;RFPFg00j[RGP;g00kbRHFbp=]P<P5PFPFPGP=P5PFPFPGP?P0g01GYRIP:ClPHFbP;Ftp=KP:P5PFPFPGP;J0Tp=cP=P5PFPFPGP0P:P;Gup=mA;?:;p=5180:/D;p==10:;,60p=R1>:;9;=0p>02P@P@P?P?P8P2P2P=g00gmP0P:P;M<kp=JP@P?P?P?P2P2P>P<P=P0P:P;M<kp=XP?P?P3PCP3P4P>P<P=P0P:P;M<op=i10:;,00p=qP0P5PFPFPGP?P:PIP;ClPHFbp=P1~?;p=YB0]?:;p=Cg01Hm-0\;p=_g00i0RI??:;p=^P4P5PFPFPGP>P<P=P5PFPFPGP0P:P;GuGup=[P0P5PFPFPGP?P:g00k;P;ClPHFbp=IP:P5PFPFPGP;J0[p=e20ZB;p=OP?P@P?P?P9P<P2P=g01H@P0P:P;M<kp>00A;?;Bp=gP0P5PFPFPGP:P;Ftp>0<P0P5PFPFPGP:P;K0Yp>03P=P5PFPFPGP0P5PFPFPGP:PHFbP;Ftp>0Jg00>ZRH#\R5#\R9#\R3$06R8#SRJ#xRKPJ%\3#\#\R3$06RL#SRM&0^JRN[RO12L:RP17J=RQ#1RR%p5RS%p3R3+0ERT3912L0RU/8PRV17J<RW#1RX,0U7EPPNP<P=P>P0PJPJ12L=RY,MUS00P>20X8BR8D<EA[[^4M^2M]3S01XPK&04JRZ,7JR[#1R\=9PTS0210U\9EVPR]18YUR^%1AR_,0YR`,6URa'D10YB9E^URbP^PaP^P;X4?RaPBO1Rc,0YRd,6U%W^Pa16:;#WXI?X4?S03PUPU%4UP`PdPaPaPaP?P?g01Y610:;H0I#4X3?XD?RdPYPY%4YP_PcPaPa%1;S04#4X4@Rc1V?BH0HM:QGhEfP;CNPb%`[%G\20@S3R\%USRb%G3%UTS05[[R_%GSR`g01YZR^B0>S3:UWJR3%GT\^S06^J`R`p-0R^&04IRe%xIRI1j?0Rf&0;?Rg7@:S07?@0g&08?Rh&07?RiPiPi1d?5Rj1d?9R91v?BRk,:j,T9,]iDK&0WFRF1ci<Cm20ViGRGP;P0g00@eRlg00AERm'V20U;0=;lmdB0S?B:H0RRnb9b:b;X0?X1?W@18;:S0810;B7E:P=[^0?^1?^@^P;PNPEPDPZPCPJPJ12LCRo12LDRp'MS09PZP8D<EAPoPpP<O4b8b5b6b=b7W?WBX4MX2MX3OQ01A?J><S0:,7J#1Rq=9PTA?J4>Rr,7JS0;#1S0<,0U9EVP20QUY15UYRs%ss+0OP712L<R7,5YRY%sYPNPlPNAHL;4f:RY,>JPCP;O1n0100000020000X2M%pHRsg00??60NLRt9LL>PDP<PJPJ12L>Ru,M7A?JEDP8D<EAP;157uS0=g01XXR7%S;Rv%S:RwP6%S0?;:;12=012=:'5R6[120:120;'5%S=?;0:[Rx%S<?;=0\6B0M0:;P;n2001000000120000000WOWNWDPx^Ow^Nv^D7P;PLP4PCP:O4bEA;M>4PMPC12L;R7f;Rv,7JRw#3S0>#1S0?,0pS0@,675=p12LER7,5PPNPlPNAHL;vf?S0A,>Jf<RxP;O1n0100000020000X2MR6ALLYtRyf=RzP0PJPJ12LYR{,MUf>R|=?JzR}P8D<EA]F]?X4M17JYS0B#3S0C#1S0D,0oR~,6o9=oo15ppP?PBPNP6PyPzPYPJPJ%a;P}P8D<EAXA?P1PJQ0112LvR117J:#3#1;9T12LxR}17J0#3#19R}}7=}PNPlPNAHL;|fBS0E,>JQ0AP;O1n0100000020000X2MALLztP=PzP@PJ%aBRyfAR6PJP;P<P8CZn0110100020010100,>JEA]?]B]CPxQ02PNP<P=PZP0PJPJQ00PZP8D<EA\][^4M^2M^3O%3[#1R[=9{TAR11[9=11PlPmPNPlPNP;1>J6S02P|PzO1n0100000020000PJP@PJPyP6PJP;PZP8CZR[n0110100020010100H02XGlP@PJPyf@R]P[n0110100020010100,>JR[,VNAHLxx201LxEFPNPlPNAHL;zQ02P|P;O1n0100000020000X2MALLxtPZPxP[EAeW?WBWCA?J<=S02,7JR[#1RZ=9PT10Uq9EVPPNP<P=PrP0PJPJQ00PrP8D<EA[[^4M^2M^3O12L|S0FA?J0:,7J#3#1;9TQ0A,2LRVA?J=0,7J#3#19RVV7=VPNPlPNAHL]]RVfDRP,>JP6P]O1n0100000020000P@PJPyfERUPJP;PrP8CZn0110100020010100,>JRr9;N;XQNPlPmPlPNP;1>JURmQ0EP6O1n0100000020000=;NrXGlP@PJPyPPPJP;Q0:P8CZn0110100020010100,>J,VNPV201L]EFPlPNAHL;6PmQ0EP;O1n0100000020000X2MRmALL]tRVQ02P]CrQ02PmPVP]P?12L]Rm/0sRPA9;qTXA?%3QS02#1S0:,0PS0G/8T10RsRq,0PRr/8TPa18:;#WXI?X4?S0HQ0GPrPaPaPaPdPPPP%4PQ0:PqPaPaPcQ02Pq10;sS02X4?RqPQPR%4RCJEXM:QPTPT%4TS0:Gi18mmRR%3[S0G#1S0I,0mS0J,6mRQ'DAqmZs9ERmS0KPRPQPRPaPqPZO1S0LO1RQ,0mRr,6m%WRPaQ03PmPm%4mRRQ0JPrPaPaPaPdPmPmPRQ0IPQPaPaPcQ0GQ0LPqP[PZ%4ZCJEXM:QGhEfP;CNS0LQ0K12L6R[%3WS0G#3S0I#1S0J'0RQ/8T10Xs/0s=9[TRRPaQ0HPQPaPqPqPXO1RQO1RmO1Rr,0[PaPaPaPdP[P[%4[Q0JPrPaPaPcQ0IPmPqQ0GPQPqPWPX%4XCJCJEXM:QPTPTQ0:15TTeS0:GiP0CNS0GPRQ0;#`S0;Q0<#GS0<17J4RX#`S0I%1X#GS0JP\P_P3P`P;P=O1S0MQ06fHfGO1S0NPNP<P;P4O2X2bS0OQ05^2bS05PePIQ07PhPi1d?HRb1v?sRX,:jRW/:X':1v?S>0G?LRS5PiPF1:bXRQ/:W=PiSCmPGPnb9b:b;X0?X1?10:sRm/0s=9;T100sRr=9mT[^0?^1?P;17Jz#1S07fJ,2LS0PPDO3b8b6b3b5b5b6bHb=b>b7C|A9PZTe12LVS0QQ0LQ0KQ0GPRQ0;Q0<Q0IQ0JP\P_P3P`Q0MQ06Q0NPNQ0OQ05%3ARV#3S0R#Y%YVS0S1~?ARA'C'CRV#_/^ePIA@f0g?@:gPhPiAPik9PFPi1:9XRZ/:X,:b=PiSPF1TQS,]iS0TF[PGPnb9b:b;X0?X1?%G:10rs=9:T16rT[[^0?^1?P;Q07Q0PP4PDO4b8b6b3b5b5b6bHb=b>b7,{]S07EFP?PP16[;XA?Q0LQ0KQ0GPRQ0;Q0<Q0IQ0JP\P_P3P`Q0MQ06Q0NPNQ0OQ05PePI1j?:Ph1TbQ,]iPGPnb9b:b;X0?Q02,6;^0?P;Q0PO1b8b6b3b5b5b6bHb=b>b7Q0QQ07EFJ0DEFW?WBWCXZKXXJP:P;O2n10110501020121102105PvPCP:O3PNPlPNAHL;Y1>J|PvP;O1n0100000020000X2MALLEtPxPEPJPJPyA?JzxS07P8D<EAe1B77&0C7EFWFW?P4P;P<P:L0BbEWFP;O1Q0=#s12L4Ry/8uR|17JERR#3S0=#1S0Q,0yS0P,6uS02'D%1RRP=qys9E|uS05P|Q02P|PaPqPPO1S02O1S0O,0yS0N,6u%W|PaQ03PuPu%4uQ0PQ0NPaPaPaPdPyPy%4yS0NQ0QQ0OPaPaPcQ0=Q02PqPRPP%4PCJEXM:QGhEfP=CNQ0518~TQ0B#1RP=qosS05/8TRRPaQ0HP~PaPqPPO1RuO1R|,0oS02PaPaPaPdPoPo%4oQ0DP|PaPaPcQ0CPuPqQ0BPP%4PCJEXM:QS0BPTPTQ0:GiP>CNPR%`w%1wRR#GP\P_P3P`PxPYO1PNQ0R#3S0R#3S0C#Y/CV#_/^ePI1j?=RV?@=g?@:fPhPi1:bZRZ=PiSPFPiPiPiPb%zH,d?RP1TPZ,]iDKPFPiAIiPb,eiPFQ0TCmF[PGPnb9b:b;X0?X1?X<?10;rS0T/8T10=sRZ9R0:9=:015=0g01KBS0D[16ZT[[[^0?^1?^<?P;17J]#1P}12LzR]P>P4PCO6b8b3b5b6b=b>b7,{4ALL4t,2L10ys'5PNPJPJALLCtS0=,2LS0O,MyPYP8D<PJPJQ09A?JxvS0QP8D<Rt9;N;XQNP?10osRuPJPJ1Mo;PvP8D<=;NtXA?1ByuRt#aS0P#3S061ByoR|#aS0M5;@S0J%OtS0I/0sS0<%O|S0;'5P@P?%y@P2%y?%1:Q04'5A;@:;20A:;40?XI@X4@Q06Q0<PqQ0PQ0IPa%O;X4?R2PtPt%4tI00CJQ0MQ0;PaP2P|P|%4|I00M<o18oyR|16y~R2'DQ059E|yRtP|P2P|Q02,6y%W|PaQ03PyPyQ0NP~Q02Q0BGhEfP<CNR~PtQ0@/8T10Rs=9pTRyPaQ0HQ0@PaPqPRO1R|O1R2,0pPaPaPaPdPpPp%4pQ0?P2PaPaPcQ0>P|PqPwPR%4RCJEXM:QPTPTQ0:GiP4CNRwPy17JxRq#`R|%1q#GRq1B7{Rc,wB%Uc%OcRa/5c'D%ga9=cB'n1B{1#OP?10}s,B1R1,wB%U1%O1R{/51'D%g{9=1B'n10]s,B}#OP?P\P_P3P`P6Q0AO1PNQ0C#3R}#3#Y&0=H-0F?RH%Y}R}5}?Q0R#YR1/CA'CR{'C#_Q0SA}?H1/CARA'C,C}#_1C}A#_%_{/^e'^'^'^PIA@V0gR{1j?<?@<g7@:PhPi1ci4%z5,d?R5/:X:05?9RA9Iib60<iPiPiPAPkAIibkDK603iPFPiPiPiB05?95RA,TkAIijAH0JPiPiPAPk1ciCDK603iPFPiPiPiP5P91ciDDKPFPiAIi95,eiPFAIiQjF[F[PGPnb9b:b;X0?X1?X<?XM?X@^XK^XL^1B0ZR5,5;,D<%g;9=5B'n1B=<R5#U1505'DA=5B4'nA=><D15>4Q0D[10<s/5>[[[[^0?^1?^<?^M?^@^^K^^L^P;Q0E,2LR517JU#1/0s5R[%g4105s,B[#UP5P[P4P<P>PCPYPxO;b8b3bVbWb]bSb\bRb=b>b7C|Q0JP@10ps,Mo#3R[PNPJPJ107s,MpPxP8D<PJPJP;Q07P8CZH02XD@PJPJP[Q0QP8D<,VNQ09P;J0KbEQ0OP;EFPlPNAHL;D1>JxPEP;O1n0100000020000X2MRxQ0=PYP4CrPEPxQ0=P4P?Pu10;RRR/8TXA?P~PtPwPyP|PqP\P_P3P`PzPvO1RvPNPePIA@{:gPhPi1:bW=PiSPFPiPiPiPbP91ci>DKPFPiAIi9b,eiPF1:Qj=PiSCmF[PGPnb9b:b;X0?X1?X<?X@^A9;mTA=:=<15<0Q0D[A9Z<T[[[^0?^1?^<?^@^P;Q0F17J6#1R6/0s5R]P]P6Q0FP>P4PDO7b8b3b5b6b=b>b7Q0OP;EFP?Pu16oR9=;oXA?P~PtPwPyP|PqP\P_P3P`PvPNPePIA@f:VPhPiPiPiPbPj1:PX,:b,Tj,]iDKPFPiAIijb,eiPFPiPiPQPj1:QP,Tj,]iDKF[PGPnb9b:b;X0?X1?X<?Q08Q0T7E:150:Q0D[AR=r<9=r=[[^0?^1?^<?P;P6P]Q0FP4PDO5b8b3b5b6b=b>b7Q0OP;EFO5EFbUWTP;O1n200110300021110411101b[PNP<P=A?JC4RCP0PJPJQ00PCP8D<EAeW?WBX4MX2MX3OWCXYKXGJP;I0LWPo"). Qed.

Lemma pf_wbytes_outside : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m a bs x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "h01Hh13Hgeh23Hlth33Hnwh41ah52bsh61mh71xp;1p;2p;4p;3p;6p;5p-1p10000p4p710p9p1000\p4p710p10019p4p710R0p8p1001Wp4p710P0p8p101Z6p4p710P0p8p10022p4p710P0p8g004Dj10Tg005Nj19Tg00OXj18Tg00Xej1;Tg0031j1ATg01W?j25Tg00Q<j23Tg00RRj12Tg00SOj21Tg005lj17Tg01R7j2:Tg00Wij24Tg00n:j26Tg01AIR0j2@Tg024bj4?Tg008[j3>Tg02SNj6<Tg02USj5=Tg00>Z#0R1#0#0R2#9#8R3#;%02#0#0R2#9R4#8R5%A3R6[f1,54R7f3R8,33#2'1%71%72':'4f2,54R2,67f4R1,33#2,12/47'@P01548R0,62f5R7,33#2,10/42P7P1f6R2P8C?P7P8O15>6f0R61541R4,60f7R9P2P7P1P8P6E<W2P6O11332#2,14/40P9P2P7P1P6D=W1P6O1n200100000021000010000W0W3X75X45W6W5o"). Qed.

(* [comment removed for export] *)
Lemma pf_mem_frame : forall k mem e c s i (a : word),
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  (bv_unsigned a < e - 4 * (i + Z.of_nat k) \/ e - 4 * i <= bv_unsigned a)%Z ->
  pf_mem mem e c s i k a = mem a.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "h04__x1h14__x2h23memh34__x3h43Ha0h53Hk0h67__arithh74__ffh86__sat8h96__sat9h:8__varmaph;5__with<4cstrh=1nh>1xh?2Hah@4__x4hA1ahB1chC1ehD1ihE1khF1mhG1shH2HehI2HihJ2HkhK1yhL1zhM2IHhN1op%0p&0p;1p;2p;7p;3p;4p;<p;6p;Bp;8p-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p710P1p8p101Z6p4p710P1p8p10022p4p710P1p8g004Dj1ATg005Nj1hTg00OXj1dTg0031j1lTg005lj1HTg00RRR1j15Tg00WiR2j21Tg01R7j2pTg00n:R3j26Tg01W?j2BTg00SOR4j20Tg02Hfj7YTg008[j3LTg00:Hj2XTg00Q\R5j1<Tg00S2R6j2>Tg00m]R7j2?Tg00m7j2UTg00Slj2|Tg021Dj2yTg024bj4wj3}Tg00oWj1MTg01AIj2KTg00dcl<^Tg02VTj6]Tg00V]j4\Tg00WDj1jTg01T;j2iTg01Tck30>Tg01:Zj2FTg01<7k20=Tg01<`j3PTg01C5j2ZTg00XEk10<Tg01Caj3STg00Xek10;Tg00YEj2OTg015Ck107Tg00Yck106Tg00ZAk105Tg00[Oj2JTg00Zlj2NTg01UGk304Tg015ak102Tg00^Gk201Tg00^ik200Tg00_Uj3{Tg00`4j4zTg00`fj4cTg01=Ij2bTg004ij1aTg01DAj7xTg00nVj2vTg02><j2uTP0j6ITg00Q<j2tTg02W<j2sTg02XEj6rTg00c7j4~Tg01SXj4qTg00d>l<eTg00cXlBWTg01BLj3oTg01?Fk403Tg00]8j4fTg00]cj7gTg00\Uj3nTg00\2k308Tg01EIj3mTg01@Hk809Tg01Dek70:Tg00KER0f0R8'1p=9f2R9f1R:/08'>p=@1>:8,?9p=4169:/K8p=:g00<TR;P;g01Y6P8Cqp=T1X;8p=2g00eHR<P;P;P;P1P1f5R=f4R>f3R?P9P:P8M<ep=VP;P;P;P;P;P;P4P8P:P9P4P?P>P=f6R4f7R@f8RAf9RBMBWp=[P;P;P2P@P2P4P=P>P?P9P:P8M<^p=RP<P<P;P;P5P1P1P?g00gmP9P:P8M<ep=`P;P;P;P;P;P;P6P8P:P9P6P?P>P=P4P@PAPBMBWp=_P;P;P;P;P;P;P7P8P:P9P7P?P>P=P4P@PAPBMBWp=kAo;:8p=GP;P9P:P8H03p==P;P:g01G2P8Cfp=CP:g00i\R7g00j;R6P6g00j[R1P8g00kbR5Fgp=EP9P7P6P6P1P;P:g01GYP8CfP5Fgp=8An;:8p=3B08;:8p=;Am;:8p=DP?P7P6P6P1P9P:P8L09p=7P9P7P6P6P1P:P8K0:p=Qg00>ZR5#AR2#ARC#ARD#ARE#A#ARF#hRG#dRH%hD#dS00#lRD[RI%9:RJ%HCRK%5@7@9/1=%H2RL%HFRF'pRM,64RN1BG?RO%5B,0>94@KA4@K>/1ORP3:PBPAP@P4P=f:RQP>FYPBP>O1RR5LD[[[[^AH^D;^G;^B;^C;]2S01XE<g00hQRS#5RT9@K9/1=10>T94@K=:OP1XDRW?XHNWJXIJXAHXD;XG;XB;XC;X2IQ01%<A#59@K9/1=%<Q#5,0>94@K=:OPPDPB%H5RP,0=S02,>KS03,?ARO,UGRT%<SRU#<RV#<RW#<RX%HE,|@,UGS04'yREP>CwPQP=O19LD8XNDPEPBPTP>P<PX104P94BK,UG,BGS05%58RY'0S06/1MX=<P;PO%5XRZ,08S07/1MXL;10OZR[/1MS0810OKR\/1MP8X>;R]11:8#MXK;X>;S09P[P\P]P]P]10:8#T#2XF;X=;R^POPO%2OPZPKP]P]%2YX><RYPXPK%2KRZEVM:[S0:PMPM%2MGR1BG>R_f;R`#<S0;#5Ra,0=Rb,>KRc,?ARd'6ReA4AK=/1_Rf'K%5`Rg/0P,0=94AK=:_fRhPePfP]108PX>;RePgO1RiO1Rj,0=Rk,>KRl,?ARm,6_PfP;P;P3P]P316:8#MXK;X>;P_P_%2_S0<PdPmP]P]P]1?:8#T#2XF;X=;PAPA%2APcPlP]P]P]1>:8#T#2XF;X=;RlPKPKPZPbPkP]P]P]P^P=P=%2=PaPjP]P]PYQ0;PiPeP`Pg%2gC`EVM:[M:_M:kM<^%MfE]P8C\RfPhf<Rg#<Ri#5Rj,04Ra,>KRk/1B%5gRb/0P9@K4/1BRcP]Q09PkP]PePbO1RkO1Rm,04Rd,>KP]P]P]PlPKPKPZPaPdP]P]P]P^P4P4%24PjPmP]P]PYPiPkPePgPb%2bC`EVM:[M:_PBPB%2BGRP?C\RbPcf=Re#jRk%5e#9Re1iLFRi160L%9F160M[[RY%9LRmg01YZRjB0>LF:UW?RF%9M\j^?mRmf>PBO1RjPDg00i0R^1F;VRV20=;KRd1F;U5P;RU1F;SRS'G'Gg01HmRa'Z&0<^RZ3SRl&0;^R31O;9Rn&07;Ro7=:&06;Rp&05;Rq1J;5Rr1N;L>04;GRL'C,EqRs&026RtPq1N;0Ru1J;2Rv58qS0=Pt1N;KRw1N;PRx,3vRy';,DrRz/3w=8qLC7C7201q1R{P8P9g00@eR|g00AER}'X20089=L|}dA{;0:CzR0b7b:b;X0;X1;168MS0>%99R}10?PR|949KS0?/0K/1M[[^0;^1;P8Pgf?R~PAPQO4b6b2b8b9b<b5b4CcQ08e1BGTS08PfPhPbPcPkPePiPYPFPmPjPD1F;W9P;dAP;dS'G%<X,F;,GS/Za'b=S^lP31O;?Rl?=?o9=n:PpPq%a2,J;R298quRWPtPq132xR2,3v,;w=8qrPtPqPsPtPqQ0=PtPqP7P6P6P1A8quz1CzL,EqFxC7C7C7C7P{P0b7b:b;X0;X1;X3;A@K9|Rz/1:169M%9>Q03,?>RL#916LM'v[[[\}^0;^1;^3;P8fB#5R}PgP~P>P=PAPQO7b6b2b8b9b<b5b4,uOS03EIQ00/tES00Q04,sXRLEIP<PX1BG=R1Q05Q06/113:X=<P;POQ07/119:18XL;16_ORO11[_R1'KR611\_R7,KOPOP1POP7%MOP]Q09P[P\Q0:P_P_Q0<GRE]PfPhPbPcPkPePiPYPFPmPjPDAP;dV/GU1F;X,GS/Za'b=S^ZP31O;>R^?=?o9=n:PpPqPWPtPq%a5,J;R5/32,;w,Dv,Cr,Eq1;w5,Dv=8qrR25QqPt135xRW,;w,DvRa,Cr,Eq13aw=8qr5QqC7C7P{P0b7b:b;X0;X1;X3;X@;%9?10>PRS,0?949KA49K?/1:5::A4?KSRS10SK/195:9[[^0;^1;^3;^@;P8P}PgP~1BG`RGP>P4O6b6b2b8b9b<b5b4CcP6eQ08Q03EIQ00PLEIErA}BTEREPA10@4RTP4Q02P`P>FYPQPEPAPTP4Q02P>PfPhPbPcPkPePiPYPFPmPjPDPZP31O;:RTPpPqA8qurPt13rxRE98quC7P{P0b7b:b;X0;%9810:PRP#9[^0;P8PgPQO2b6b2b8b9b<b5b4PfPhPbPcPkPePiPYPFPmPjPDPZP3A=n:lPpPq13ry,;w=8q5Pt13Ev,;w=8q5C7P{P0b7b:b;X0;X1;X3;A@K8P/19A@KP9/1?[^0;^1;^3;P8P~P}PgP=O4b6b2b8b9b<b5b4PfPhPbPcPkPePiPYPFPmPjPDPZP3PTPpPqPsPtPsC7P{P0b7b:b;X0;Q0>16:M[^0;P8P~PAO2b6b2b8b9b<b5b4PfPhPbPcPkPePiPYPFPmPjPDPZP3A=^9o?=:lPpPq1J;CRC/3x,35,;w,Dv,Cr,Eq=Qq2Pt13WC,;w,Dv,Cr,EqA8qar5QqC7P{P0b7b:b;X0;X1;X3;X@;1?:zA4:K9/185:810|>949KQ0?/1:5::[^0;^1;^3;^@;P8P}PgP~PGP4O5b6b2b8b9b<b5b4O:EIPBPAP@P4P=Q0;P>FY=LDReW?XHNWJXIJXAHXD;XG;XB;XC;X2IWMXE<P8C~XE<o"). Qed.

Lemma word_to_le_bytes4_Z : forall v, word_to_le_bytes 4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "h01xh12Hah27__arithh34__ffh46__sat8h56__sat9h68__varmaph75__with81mh91nh:1vh;1yh<1zp;1p;2p;3p;4p;<p;7p;6p;Bp-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p710P1p8p101Z6p4p710P1p8p10022p4p710P1p8g004Dj11Tg005Nj1;Tg01RTj2DTg00OXj1@Tg00Xej1<Tg00Q\j14Tg00TIj28Tg008[j35Tg005lj13Tg00RRR1j1:Tg00S2R2j26Tg00WiR3j20Tg00oWj1=Tg01SXj4[Tg00:Hj22Tg00dcl<TTg01T;j2NTg00n:j29Tg01R7j2ITg01Tcj3HTg00XEj1CTg015Cj1ETg00Ycj1FTg00ZAj1BTg00Zlj27Tg00\2j3GTg00]8j4ATg00]cj7JTg00^Gj2KTg00^ij2?Tg00_Uj3LTg00`4j4MTg00`fj4>Tg01S:j1OTg02YOj4PTg00m7j2QTg01W?j2RTg01Wij2STP0j6ZTg021Dj2YTg00d>l<XTg00cXlBWTg00eHR0g00<TR4P4P4P1P1f5R1f4R5f3R6f2R7f1R8f0R9M<Xp=VP4P4P4P4P4P4P2P9P8P7P2P6P5P1f6f7f8f9MBWp=UP4g00>Z#1R1#1R5#1R6#1#1#1R2#;R:/D9%;6#@#<R;g00hQ#4#4#4#4R</89R=18<835X<4P<P:P9%36R6%:<R>'6R?%32R2'0%35R5,66R@/02RAP4P4P3P9X04RBP31089#=X;4X04P?P@PBPBPBP4P4g01Y61689C[,24X84X94P6P61246P>P5PBPB%:9,24X00P<P51245EVM:UP2P21242M<T%31R1/N2g00KER0/9110021I12RB,90[[1001R>g01YZR@AH128UW1100B\@^1>g00i0R>#C%<>%E4%F4%B4R>g00i\g00j;R@P@g00j[R@P4174617455G4g01GY1742CAg00kbFJ1K>@P9P7g00@eR@g00AER>'21?97=5@>dAL408CMb3b6b7PAP9b2b4b5C>%O:,0?eCP1Q:9R?,R:1S:9EZ1Y<?=5;=eX:4o"). Qed.

(* [comment removed for export] *)
Lemma pf_mem_cell : forall k mem e c s i j t,
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= j < Z.of_nat k)%Z -> (t < 4)%nat ->
  pf_mem mem e c s i k (Z_to_bv 64 (e - 4 * (i + Z.of_nat k) + 4 * j + Z.of_nat t))
  = Some (nth t (Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16)) (Z_to_bv 8 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "p'0h04__x1h14__x2h24__x3h31Hh42H0h53Ht0h66__sat9h74cstrh86__sat8h95cstr0h:7__arithh;4__ffh<8__varmaph=5__with>4__x4h?1zh@4__p1hA1xhB2HjhC4__x5hD1jhE1ni001nhF2HkhG1chH1ei011ehI1ihJ1khK3memhL1si021shM1thN1yhO2HahP2HehQ2HihR2HthS7__sat10hT1mhU1ohV2H1hW2H2hX2H3hY2H4hZ2H5h[2H8h\3Hj0h]3Hk0h^3Hneh_2IHh`2e0ha1lhb1qhc1rhd2s0he2z8p%0p%1p&0p&1p;1p;2p;3p;4p;6p;<p;8p;7p;;p;Bp-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p710P1p8p101Z6p4p710P1p8p10022p4p710P1p8g004Dj1UTg005Nk10LTg00OXk10CTg0031k10WTg005lj1fTg00RRR1j14Tg01R7k20^Tg00n:R2j21Tg00Q\j1DTg00l_R3j2nTg00SlR4j2:j1{Tg00m7j2HTg008[j39k10<Tg00V]j4dTg00nVR5j2KTg00:Hj2CTg00o1k30ATg00oWk10@Tg0105k60=Tg00SOR6j20Tg00S2R7j27Tg00WiR8j25Tg00WDj1bTg01T;k20NTg01Tck317Tg00m]j22Tg010^k20}Tg011Ok20xTg0120j1xTg012Ij2jTg012ik20oTg013Pk20lTg0147k20kTg014]k20jTg00XEk10gTg00Xek10FTg015Ck10fTg00YEj2gTg00Yck10eTg00ZAk10dTg004ik10ETg00[Oj2^Tg00Zlj2vTg015ak10cTg00^Gk20bTg00^ik20aTg00_Uk30`Tg00`4k40_Tg016Cj1TTg00gmk10BTg016ak601Tg017=k20]Tg017]R9k20\Tg021Dk200Tg024bj3~k40[Tg01W?j2sTg018=R:j1lTg00TIj2ck116Tg0089k10Yk204Tg018]j4Zj3qk20>k10XTg01@lj2oTg00U]k20VTg00V@k30UTg00dcl<mTg0199k20STg01AIj2eTg01:Zk20:Tg019[k10RTg01:9k20QTg01Ack30OTg00`fj4|Tg01;Cj8@Tg02ZVk115TP0j6Xk70pTg01<7k214Tg01<`j3zTg01=Ik20|Tg01UGk30{Tg02><k20KTg00Q<k20vTg02W<k20sTg02[bk60rTg02Hfk70ITg02\km;0qTg00c7k40nTg00d>m<05Tg01SXk40mTg00cXmB0JTg01?Fk40tTg00]8j4hTg01?dk60uTg00]cj7yTg01@Hj8tTg01BLk30iTg01C5k20yTg01Cak30zTg00\Uk30hTg00\2k30~Tg01EIk310Tg01DAk711Tg01Dek712Tg01Elk613Tg00KER0f0R;'5p=3f3R<f2R=f1R>'0'7/5;p=M11>;,K=p=8f6R?f5R@f4RA/0<'7'217=>'0/0;p=Ff7RBP?P@PAP<P=1H>;K0Ip=J12=>/2;p=i17>;,0=p=kPAP<1c=>P;CZ-04@p=Ig00<TRC/C;p=<g00eHRDPCP3P1P2g01FPP@PAP<P=P>P;M<mp>02PDPCPCPCP1P1P<P=P>g00hQR3P0P;N<05p>0ZPCPCP2PBP2P?P@PAP<P=P>P;M<mp>0?PCPCg01Y6P;H0mp>0;PCPCPCPCPCPCP6P;P>P=P6P<PAP@P?PBf8R6f9R2NB0Jp>09PCPCPCPCPCPCP7P;P>P=P7P<PAP@P?PBP6P2NB0Jp>0PPCPCP8PBP8P?P@PAP<P=P>P;M<mp>0812=>/7;,0<p=>A9C;0p=w10>;99C=p=QA9C>;p=BPCP=P>P;H0tp=;PCP>g01G2R8P;Chp>0DPCP>g01GYR7P;Chp=uP>g00i\REg00j;RFPFg00j[RGP;J0up>03PAPEPFPFPGP<PEPFPFPGP=g00kbRHFyP>P;Gtp=]17>;,2=p=\10>;,7=,2<p=S17=>,0</0;p=}10=>/0;p=GP<P=P>P;CZ-04Ap=r10<=,7A,2@/0>/0;p=pPCPDPCPCP:PAP1P<g01H@P=P>P;N<05p>0T20:C;p=`B0iC>;p=?g01Hm-0y;p=Og00i0R:@0z>;p=LB0hC>;p=6B0~C>;p==B10C>;p=APCP>g00k;P;Chp=RP>PEPFPFPGP;PHFyp=WP=PEPFPFPGP>P;K11p=[P=PEPFPFPGPCP>P7P;ChPHFyp=EP=PEPFPFPGP>P;K12p>07P?PEPFPFPGP@PAP<PEPFPFPGP=P>P;GtGtp=N10>;,7=p=Y12=>/7;p=aPCPAP4P4P<P=P>P;G@p>0MP=PEPFPFPGPCP>P8P;ChPHFyp=PP<PEPFPFPGP=P>P;Gtp=_PCPAP<P=P>P;EXp=VPDPCPCPCP1P1P@PAP<P=P>P;N<05p>0w17<=,2A/0>/0;p>0H12=>/0;p>06P>PEPFPFPGP;J13p>0Gg00>ZRE#URH#UR8#UR7#URI#U#URJ$0LRK$0C&0L7R7$0CRL$0WRM[S00%3=RN%f8ROP<%46RPP?CM%fHRQ%fJRJ+0^RR,1BS01%3AS02f:RS#4S0378A%D3RT#DRU#DS04#DRV,nAS05f;RWPSP2P6PBf<RXPKPSPOPB%4XS06POP?%4@RYFFGJPLPLP@PVQ06%fERZ;i?=k26%fIRI':1H70R7EI59M[[[[[^MD^DC^IC^LC^GC^HC]KS07XJDQ00POP<%43R[P?CMQ01Q02?8A[Q051n@V11YOR\P@PY%<YPVPO%<OS08J02P;CdP\%3BR\11B[RY'KA8\B0R]P\PYP\P;XACRYP0O1R^,1Bp-0R_/C\A9_\\e:0A\\PY11>;$0@XNCXACS09PBPB%<BP[P^PYPY%4;S0:#<XADS0;1CC0H0ZR`L0?J0=P=CdP]102[R],7ORa/5XPOP2P0PXCMRbPY15>;$0@XNCXACS0<Pa102^Ra,7OPYPYPY17>;$0;#<XTCXECPOPOQ08P]PaPYPYPY10>;$0;#<XTCXECS0=P2P2%<2P[P^P`N:09N:0PPXPX%<XL08P@CdPb%b6%3P20NQJRP110Q%3J110R[[Rb%3QR`g01YZR^B17QJ>UWORJ%3R\^^O`R`f?R^12[ZRaPXf>R]C>Rc00}I%3c%3IfARcPaP]f@RdC>Re/:IRf#3[[PdPaf=RgP^C>00xI%wIRh#x17If1jeI5Qe[20oeI110IfBRePaP^PcC>Rf/jIRi#3?8iI[20lfI11I0fCRfPaPdPeC>Ri/jIRj,1I15j0'K[20kiIfDRiPaPcPfC>Rj/:I#w\h20jjIfERjPaPePiC>Rk/jI/Bk\h1:kIPCfFRkPaPfPjC>/jIPCP5%3i11i0fJRafIRhfHS0>fGRlPkP3PKPhPOPkP[POPj%4iS0?FFGJPLPLPiPVP=P7EI59MPX%3k11l0&0g:Rm&0F:R:&0fCRn1gC>S0@?;>n7;>&0eCRo&0dCRpPp&0EH,^CRq1vC0Rr+0D&0cFRFPpPp1urqPF203p<D]D]20bpGRGP;P=g00@eRsg00AERt'C20a;==9stdB0`C0>H0_Rtb;b<b=X0CX@_11;0%3>P<[[^0C^@_P;fNfMRsfLRufKS0APaP3PKPsPOPaP[POPhQ0>#4S0BFFGJPLPLQ0>PVP?P7EI59MPhP>P=O4b:WZWYP>P;O2n2001000000121000000bcbbbXbWbVb4b3b8b6bSb7b]b\b5WRWBWPWFXQNXMDXDCXICXLCXGCXHCWKQ07Q00POP<%D2#4P?CMQ01Q02%DW#478AQ05%4gR[#TRvPXPWPSP2P6%D]RwPKPWPOP6P;POPB%4?FFGJPLPLP?PVAi;ZB=kS2/:IP7EI59MX?CPC%Dg#4S0CA8\B;X?CP>Pv&0BgS0DJ01%3?S0E?8?vPC%4wPOP2P;PXCMX?CPA%4]S0F#TRw&0B]J01POP6PwPWCM%4^S0G-0]6Q0G,B6Rw%xw+0\P9%4dS0H,B2R9%x910WZR99\]O,HK1:gI,HK-00V5~^P]10gXPXP9PcPKP]POPW%4cS0I#TR9POPS%42FFGJPLPLP2PVAi9ZS=kgX/:IP7EI59MP;Q0I,BSS0JPC%4eS0K%3;S0L%4fR9#TRw78;10]ZS0M9\cOS0N,HKRv1:dI,HK-00VR\5~eS0OPc10d^S0PP^Q0MPiPKPcPOP]Q0?#TRxCSRyPOP>Q06C}GJPLPLPXPVPd12xZS0QP>P^C>/:IP7EI59M]BXDCQ0K#3Q0KQ0K#TS0R38PMPc10gZS0S9\dORx,HKS0T1:^IS0U,HKS0V-00VS0WPdPOPgPwCSS0X17O9Rz%4WR{3GR|,HKS0YH0[S0ZPLPLPXPVPdQ0QQ0?P^C>/:IP7EIR}99M;XUMR~PMPLPLQ0Y,sKS0[Q0T,sKS0\'2#lQ0WP7DrP~P|PLPL1sKvS0],2;#lP\P7Dr=9M}X?CPxPLPLPyPOQ0?Q06C}S0^/2;#lP\P7Dr=9M}X?C&0FLR\Q0U,cVRyPLPLQ0^Q0N'2#lP;P7Dr=9M}Xa\PLPM&0YLS0_Q0_PL12|xR}#lRvPyP7CZPLPWP^12wZS0`P9P]C>S0a/:IS0b,cVRwP7CZPM\LQ0_'CS0cPLPLAqLvyAqLWwP7P7P\PL\LS0d20>Lv20>LWS0ePyPwPDQ0d\\S0f&0XLRwPwPvPWQ0f\D/CwA9DvWPdPOPg109ZPzP{EpS0g/2xRz,o0Rw/B{PDPC&0<DP1&0<C%4>Q0:'BA9D>;20V>;40UXNDXADPvPwPY1o0;XACP}Pz%<zI0TPWP{%<{RzM<m1nWVS0h11{OR}PWP{PzPVPOQ08J02S0iP?CdRzP}%biRwQ0?#3Rv%bgR1%3[R[PfPOPd%4kRy/0ZPOPyQ0FFFPfPOPdPZCS'2Ry-0S0110y1o0yR~/By'K15y0%w~'K'ePiPOPc%4lS0F/0ZS0jPOQ0FQ0GFFPiPOPcPZCS'2,o0PCPPPbPJP`P5%4aR~#3Ry10~ZS0k,1~1B<9PB%4uS0l#3%4sRs10sZS0m'1%`URU%`TS0n20:C3R3'?'?#OQ04#`S04&0RE-0QC>0OCU/?3RT'?#O%OT/Lm'L'LP:1gC<S0o1gC@S0p7;=1gCAS0q?;@n7;>PoPp203pB1^CERT&0EES0r#U,^CS0s1vCORE1^C8R81vCZR~,6q'6'='A1=Eq'61^CHRH'6Q0s168~S0t,=E'A'AS0u'R,Wp5[pQ0u=Epr1RTr,Wp5[p607pPFPpAEprHS0uPF1RTH,WpS0vFNPGPtb;b<b=X0CX1CX2CX>CXCCX@_10<ZS0w9YO=S0x,2A17O<S0y;G>10=ZS0z,7OS0{,2A'2S0|,B;,K@Q0|/50%w;'K'e1B=<\N[^0C^1C^2C^>C^CC^@_P;PuPOPhfO#4S0|/0ZPOQ0|Q0FFFPuPOPhPZCS'2,10PuQ0|PhQ0FPBP6P2O8b:W4W3P>P;O2n2001000000121000000b6bSbeb[b9b7b5C|G@PCP\&16VS0FQ0FQ0UQ0bP\\CQ0F'CS0bPCPC%{^Q0a#{PIPIPC\CS0|P^Q0aQ0|\C/C4S0aPzP}PwPvP1P[PPPbPJP`P5Q0B#3S0}Q0BQ0B/0ZS0~'1S10%4hR4/0ZS11/2ZS12?a4i9QjjP@Q0A#4Ru10uZS0A'1RuPmP:1gC=S13Q0o7;>S14Po16H~S15/A~/AHQ0r,^CR0'=,6T,RT,WpPGPtb;b<b=X0CX1CX2C10>ZS0r/2Z?a>=9Q;;^0C^1C^2CP;Q0>PsPhO3b:W4X3yP>P;O2n2001000000120000000b8b6b9b7b5I0M%<IS16G@G@G@1CL7S17G@G@Q0WQ0U$15EXQ0\PzP}PwPvP1P[PPPbPJP`P5Q0}Q1010fZS0U9\kOS18#3Q18;8RP@214COS19=zCUQ19=zC3'?%DVS1:#`S1;,?3#O+0|Q04Q19Q0n5zC/?3S0n'?S04#O/Lm'LP:Q0o?;=n?;>nPoPpAEpr8S1<PFPp1vCQ>0{CKS1=9PpTS1>PFPpPpQ0t,6H,=E/uTPFPpQ0uPFQ15,=E,ATS1?9EprQ1?Q1=5Pp5[pC_D]FNPGPtb;b<b=X0CX1CX2C11>RS1@10AZ9YO<S1A/5=Q02PAPOP@PZCSRQ#3?8QR[[[\N^0C^1C^2CP;PsPlPaP6PeP]PiO7b:X4uX3yP>P;O2n2001000000121000000b8b6b9b7b5-0KxS02DVQ0[PzP}PwPvP1P[PPPbPJP`P5Q0}Q10PkPOPfQ11POP4Q0IFFRQ#3?8QRP@Q1:#D#`Q19Q1;5zC1?U3'?'?#O%`VQ04'?#O/Lm'LP:Q0q?;=nS0qQ0o7;>S04PoPpQ1<PFPpAEpr0PFPpAPp8ES1;PFPpQ1>PFPpPp160~S19,6H,=ER3/uTPFPpQ0uPF1AT3S1:1=E0'6/68S119EprQ11Q1=5Pp5[pC_D]FNFNPGPtb;b<b=X0CX1CX2CX>C%3<R311@O11<RPOP@10?ZPACMQ0EP?POPB106Z17O6S1BP2EpS1C#3Q1C;8R[[[[\3[^0C^1C^2C^>CP;%4jS0EPsPlPaPBP6P2PeP]PiO:b:X4uX3yP>P;O2n2001000000121000000b8b6b9b7b5-0K|S1CDVQ0ZQ0WPcQ0TQ0YPDPVQ0]Q0:'0S0:/5RXEDPx%4VS0Z,0;S1D/5RX?CQ0Z,0xS1E/5RS1F10xOS1G/5RPYQ0<Q1EQ1GPYPYPYQ0=PxPx%<xQ0ZPOPYPYQ0;PVPOQ08J0wN:09S0;PRPR%<RL08PzP}PwPvP1P[PPPbPJP`P5Q0}Q10Q18/0OS0=/5RP@Q0n,?U#O/LmP:Q13?;>nS0nPoPpQ1>PFPpQ0uPFQ1?/6ES0uQ1=5EpFNPGPtb;b<b=X0CX1C11;RS1=Q0w9\=OS0</0OS1H/5R\N[^0C^1CP;PlPaPePiO4b:X4uX3yP>P;O2n2001000000121000000b8b6b9b7b5C|Q1FeQ0\Q02DVQ0W-0vLS1FQ0V-0sVS0VEXPDPVQ0]Q0^,HK,sKRU'5Q0:78UXEDPx15;UQ1D78UX?CP|Q0N/5;S1DQ0NQ0Z'078;X?C15x|RUQ1E,1|S0Z'KS0NQ0g,5xRxQ0gQ1G'1S0:'KPUQ0ZPxQ0:1C_x:0AUxPYQ09P|Q0gQ0g#<Q1EQ1GQ0;L0?J0=PzP}PwPvP1P[PPPbPJP`P5Q0}Q10Q18/5QS18Q0=78QP@PmP:Q04PoPpQ1<PFPpQ1;PFQ1?Q115EpS1?Q11Q0u5Pp5[pFNPGPtb;b<b=X0CX1CX2CX>C11AOQ0<Q1A,2=POPAP@C}RY'5Q1H78Y[\3^0C^1C^2C^>CP;Q0EPsPlPaPBP2O6b:X4uX3yP>P;O2n2001000000121000000b8b6b9b7b5C|Q0NeQ0[Q1CDVQ0\Q02DVQ1FQ0VEXJ0rEXQ0TQ0W5~cRYPd10^]RxP]Q0SPfQ0YK0IPfPYPdPxP]Q0SQ0YPzP}PwPvP1P[PPPbPJP`P5Q0}Q10Q0U#3S0YP@PmP:Q0@PoPpAEprTRUPF16T~S0W9EprC_PGPtb;b<b=X0CQ0LQ0r#3[^0CP;PlPiO2b:S0LX4uX3yP>P;O2n2001000000120000000b8b6b9b7b5PzP}PwPvP1P[PPPbPJP`P5Q0}Q10Q0U=YO4Rr/5kS0UP@PmP:Q14PoPpPpQ15,6T,=E/u0PFQ0W/6H,=E=Ep0D]PGPtb;b<b=X0CX1CX2CPOP;Q0rP=CMQ0r=YO=S0r/5<[^0C^1C^2CP;PaPsPlP]O4b:S0WX4uX3yP>P;O2n2001000000120000000b8b6b9b7b5PzP}PwPvP1P[PPPbPJP`P5Q0}Q1011kRS14P@PmP:Q0@PoPpQ1>PFQ1>C_PGPtb;b<b=X0CQ1=Q1@[^0CP;PaPeO2b:RRX4uX3yP>P;O2n2001000000120000000b8b6b9b7b5P|PcPOQ0MQ0?CS,1;Q1D'eX?CPzP}PwPvP1P[PPPbPJP`P5Q0}Q1012kr,1QQ18'eP@PmP:Q04PoPpQ1<PF203p?Q1?607pC_PGPtb;b<b=X0CX1CX2CX>CX@_Q0{,2>Q0x,2>Q0y;GA'5,e@\3^0C^1C^2C^>C^@_P;PaPOPlQ0mPOPsQ0EFFAGlZs9\aO'1Q0EPsPlPaPBO6b:X4uX3yP>P;O2n2001000000121000000b8b6b9b7b5Q0[Q1CDVN;0qEXWBPWP;PAK0pW`P;O1Q0J#x1nSVQ03/1ORyPSQ03Q03#<PVPOQ08J02P@CdPy%bf%39%bXQ06#3PPPbPJP`P5%3dQ0j,1dPjPOQ0B9GeZ17OcRyQ0HI0HQ0~9YOe>06jyQ0H3QP2%3eRyQ0k,1fPmP:Q0qQ0p?;<n7;>PoQ15/60,=E,AT1=E8R@'6/6qQ1:/6@/6q'R,WpPGPtb;b<b=X0CX1CX2CX>CXCCQ0r,2;Q0y;GAQ0z9YO>Q0y606;;QA^0C^1C^2C^>C^CCP;Q0?PjQ0lPkPhO5b:W4W3P>P;O2n2001000000121000000b8b6b9b7b5P^POQ0K9GXZ17OWRqQ03I0HQ0R9YOX>06^qQ033QPCPdPOQ0SP917OXRqP{EpR@Q0OPcQ0PP^Q0MPiPKP;GJPLPLPXPVPdQ0QPgP^C>/:IP7EIRu59MX?CPMPLPWAi9ZX=kx]R9/:IRa,cVRlP7CZR_-04LA9M;uXUMPLPMQ0_Q0_P_PLPWP^Q0`PXP]C>R_/:IRu,cVR?P7CZQ0cPLPLAqLWlAqLW?P7P7P\Q0dQ0eQ0ePlP?Q0fQ0e'CPCP\Q0FQ0FPaPuQ0bPCPC%{9%{_PIPIQ0|P9P_Q0aPzP}PwPvP1P[PPPbPJP`P5%3cR_Q0~,1cRc124Z?aei9GjiQ12?aei7QjPS%3fRjQ0A,1iRiPmP:Q04Po16TH1A0~/A8/=H'6Q19/A~/A8/=H,6T'R,WpPGPtb;b<b=X0CX1CX2CX>C12=Z?a<>9G;>Q0z/2Z?a<>7Q;^0C^1C^2C^>CP;PkPsQ0>PhO4b:W4W3P>P;O2n2001000000120000000b8b6b9b7b5I0MQ16G@G@G@Q17G@G@PYPdPxP]Q0SPfPKP@GJPePYPdPxP]Q0SPXPWPzP}PwPvP1P[PPPbPJP`P5P_PcQ0YPSQ0LX4iX3jP>P;O2n2001000000120000000b8b6b9b7b5PzP}PwPvP1P[PPPbPJP`P5P_PcQ0UPSQ0WX4iX3jP>P;O2n2001000000120000000b8b6b9b7b5PzP}PwPvP1P[PPPbPJP`P5P_PcQ14PSPRX4iX3jP>P;O2n2001000000120000000b8b6b9b7b5PzP}PwPvP1P[PPPbPJP`P5P_PcA8ye4PSPmP:Q0nPoPpQ0v-0GpPFPpQ159PpTPFPpPUPFAPpTH9[pUC_FNPGPtb;b<b=X0CX1C1B;>g01KBRU[Q0z,1>A83<A\N[[^0C^1CP;PsPkPWP>P=O5b:X4iX3jP>P;O2n2001000000121000000b8b6b9b7b5Q0hP}Q0iPzP}PwPvP1P[PPPbPJP`P5P_PcQ0I/1OPSPmP:Q13Q0o7;<?;>nPoPpAPpTEREPFPpQ0s/R8,Wp-0GpPFPpPpQ0sQ0t+0DPFPED]FNPGPtb;b<b=X0CX1CX2C11;O1B<=PU[Q0w,1A11<O[[[^0C^1C^2CP;PkPsQ0EP2PWP>O6b:X4iX3jP>P;O2n2001000000121000000b8b6b9b7b5C|O<EXQ0X?Gq{P;J01b3W^P;O1n200110200021110111100bdPgPXPWPSP2%D^PKPXPOP2Q0G#TR2Q1B%4BEpGJPLPLPBPVAi2Z6=kWS/:IP7EI59MebFbBQ0CQ0DDVWRWBWPWFXQNXMDXDCXICXLCXGCXHCWKW_XJDP;H0nXJDo"). Qed.

(* [comment removed for export] *)
Lemma pf_mem_rdn : forall k mem e c s i j,
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= j < Z.of_nat k)%Z ->
  rdn segs (pf_mem mem e c s i k) (Z_to_bv 64 (e - 4 * (i + Z.of_nat k) + 4 * j)) 4
  = Some (Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "h04__x1h14__x2h24__x3h34__x4h41Hh52H0h67__arithh76__sat8h86__sat9h94cstrh:1xh;2Hah<4__ffh=8__varmaph>5__with?1zh@2HehA2HihB2HjhC2HkhD2HthE3Ht0hF1chG5cstr0hH1ehI1ihJ1jhK1khL1mhM3memhN1nhO1shP1thQ1yp;1p;2p;6p;4p;<p;3p;7p;=p;8p;Bp-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p710P1p8p101Z6p4p710P1p8p10022p4p710P1p8g004Dj1<Tg005Nj1XTg00OXj1WTg0031j1]Tg005lj1>Tg00RRR1j12Tg00SOR2j20Tg00S2j24Tg00WiR3j26Tg01R7j2\Tg00n:R4j23Tg00nVR5j2ATg02Hfj6~j7oTg00Q\j1?Tg00m]j25Tg00m7j2@Tg00Slj2RTg00TIj2MTg00aQj2nTg00oWj1iTg01SXj4hTg00dcl<UTg00WDj1FTg01T;j2`Tg01Tcj3_Tg01<7j2^Tg01:Zj2:Tg01<`j3BTg01C5j2ETg00XEj1[Tg01Caj3DTg00Xej1ZTg00YEj2KTg015Cj1YTg01?Fj4JTg00Ycj1}Tg00ZAj1|Tg00[Oj2CTg004ij1{Tg015aj1zTg00Zlj2GTg01UGj3yTg00\Uj3HTg00\2j3TTg01EIj3rTg00^Gj2qTg00:Hj2QTg00^ij2pTg008[j3VTg00_Uj3mTg00`4j4lTg00`fj4kTg01W?j2NTg01DAj7jTg02><j2OTP0j6PTg00l_R0j2STg018]j4gTg0089j2fTg02^0l=eTg00V]j4tTg02_4j8uTg00d>l<vTg00cXlBwTg01BLj3xTg00]8j4LTg00]cj7bTg01@Hj8aTg00KER6f0R7'6p=1g00<TR8/Q7p=;g00eHR9P8P8P8P1P1f5R:f4R;f3R<f2R=f1R>P7M<vp=dP8P8P8P8P8P8P2P7P>P=P2P<P;P:f6R2f7R?f8R@f9RAMBwp=cAx8>7p=9P8P>g01G2P7CLp=IP>g00i\RBg00j;RCPCg00j[RDP7g00kbFbp=8P8P>g01GYP7CLp==P<PBPCPCPDP=P>P7Gap=7P9P8P0P1P4g01FPP:P;P<P=P>P7M<Up=sg00>ZR4#<R1#<R0#<RE#<RF#<#<RG#XRH#W%XERE#WRI#]RJ[%1>%>0RK%2?,0='4/6:%>1RL%>GRG'\RM,32%1<RN%2A,3<'Ap,4segsPAP@P?P2P:f:ROE~g00hQRP#?RQ#?RR#?RS#?RT%2ORU,0:,4K,5@14K;'0RV,@HRW%>4RX,5U/5;/42,0?%>FRF'RRY,MT1nTYP8PV%2TRY,07/6MX?810VYRZ/6MR[10VKR\/6MP8P8P3P7X:8R]P316>7#iXQ8X:8PZP\P]P]P]P8P8g01Y610>7Ch#;XL8XN8PVPV%;VPYPKP]P]%27#;X:9PTPK%;KR]EdM:cPMPM%;MM<U%FORY%1URU1`LGR\136L%1G136M[[RZ%1LR3g01YZR^A_LG>UW;RG%1M\^^;3R3P5%1?R^f=R_#2R`,3?Raf<Rbf>Rc#2,0A,4K'514K@Rd'0Re/0K/6MP<%1ARff@Rg#2,3ORhg00i0Ri1^8KRj1:8SRS5B81:8RRR1:8Q9B8j1:8PRP'9RQ'9'9g01HmRk'E%[iRl3D%ZiRmP8P81K8;P=%Y8CJP>1K8<CJRn%}8Ro%|8Rp1C80R0%{4,C8Rq'I,8pRr%zCRsPp1C84R41G8L=y8HRL'I,8pRtPsPp1G86Ru1C81R1'=,8pRvPs1G8KRwAH81q5T8R19r84AT8w05H8Rq=H8w/=L,8pC7C7C71qpDRwP7P=g00@eRxg00AERy'Q1p7==VxydAm86>ClRyb<b=b>X08X18X28X3813<=Rx13>M10;:,4KRz,5<14K2R{'0/0K/6M\N[[^08^18^28^38P7PbfB#2RNP_PgP>PAf;R|O7b6W5W4P>P7O2n2001000000121000000b7b8b9CkP[e1NHWPYPUP\PZPGP3P5P^Pa%1e13eM'AP<%?T,:89B8j19SQ'9/Ek1:8T9B8j19RP'9/Ek=Dil5DiPmPnPoPpPrPsPp1=u0,8pPsPpPtPsPp1=14,8pPsPpPvPsPpPBPCPCPD1=uq,8p1IqL,8pFjC7C7C7C7C7PwPyb<b=b>X08X18X28X38Ry%1;13=M16z<%1:102?,4K,5:/0dRd#113dM'A[[[[\x^08^18^28^38RxP7PbPNP_PgP>P=PAPOP|O9b6X5hX4fP>P7O2n2001000000121000000b7b8b9,OVEP1S7TP8%2b,0?,4K,5O/0{R{PbP|POPAP@P_%2=,07,@HFoPIP=15`X/5?/4A,0O/RF,MT1@E6Cg,fI5VJX?8PbP|POPAP@P?P2P>P:P;P<P=P7M=e1@H{,NH1S>T%2>RH/3KR;P>PH%;HPTPKP]EsP7CtP;%F_%1`%F<%2<#1P\PZPGP3P5%1|fAR5#2,3|10_N,4K,5g14Kb'0Rb#113bM'AP?%1_fDR?#2,3cPyPxP7PgfF#2P5P?P>P=P_Pcf?O9b6W5W4P>P7O2n2001000000121000000b7b8bGb9bE,O{EPWDXP9GuWBW@WCWAXJ8XI8XO8XF8XH8WMXK9o"). Qed.

Lemma pf_cell_linear : forall c s k j, (16 | s)%Z ->
  ((c + (k - 1 - j) * s) / 16 = (c + (k - 1) * s) / 16 + j * (- (s / 16)))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "p'0h01Hh14__x1h24__x2h34__x3h41zh57__arithh64__ffh76__sat8h86__sat9h98__varmaph:5__with;2Hah<4__x4h=1sh>2H0h?2H1h@2H2hA2H3hB7__sat10hC1chD1jhE1khF1qhG2q0hH1ri001xp;1p;2p;3p;4p;6p;7p-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p710P1p8p101Z6p4p710P1p8p10022p4p710P1p8g004Dj1:Tg005lj1ATg02`;j2TTg00S2j22Tg00m]j28Tg00Slj21Tg02`[j14Tg01T;j2QTg00n:j2;Tg01R7j2hTg01Tcj3eTg00XEj1]Tg00Xej1ZTg00YEj2HTg015Cj1WTg01?Fj4FTg00Ycj1VTg00ZAj1UTg00[Oj2?Tg00Zlj2ETg01EIj3ITg004ij1STg00\Uj3<Tg02a8j2DTg00^Gj2PTg00:Hj2OTg00^ij2NTg008[j3>Tg00_Uj3MTg00`4j4RTg00SOj29Tg010^j2LTg011Oj2gTg0120j1fTg012Ij2=Tg012ij2dTg00nVj2KTg013Pj2_Tg00Wij2JTg0147j2\Tg014]j2[Tg01Elj6YTg02a[j3^TP0j6GTg02b<j4XTg016aj6`Tg00\2j3aTg00]8j4bTg00]cj7cTg00<TR0f1R1f0R23>p=3f3R3f2R4/81/22'9p=@1212,94p=0g00KER5/J2p=6Aa012p=7P0P1g00k;P2Cbp=BP1g00i\R6g00j;R7P7g00j[R8P2g00kbFcp=Cf4R918341212'2'9p=5g00>ZR:#:R;#:R<#:#:R=#AR>/T4g01^8P0122>R?,39X40f5R@%A:RA,83RBP4P9C@/1>A0@B9/1>119>#4704'3P2f6RB/3?P0121>R?f9RCf7RD/8ARE/8BRF;02/1>A0CE2/1>112>RG#470B'3X=0%A;RH%:=#:#AR='QRI1;5H%6=1hH=RJ,;5[[RK%6HRLg01YZRMAeH=1UW;R=%6J\M^;LRLg00i0RM#]RJ%ZMRMP0P01H09P4%W0RHCFP11H03RNCF%V0RO%U0RP1?0:RQ1?0;R;1E0A5I0RR%S:,?0R:1E0>RS'7RT'75<01?0<R</7:,D0/7S5<0AI0R</7T9<0Q'B'C1PP8RTP2P4g00@eR<g00AERR'O1N24=><RdAM051CRRRb6b9b:X10X20X30X<0181AR<124>RU5021234#4;0>P2P<P3PUC@'3^10^20^30^<0P2f8R<P9PCf;RVO4b5b7b818BARW=0<?12@1#4;0>P<PWP@P?C@'3P0A0CEURE12B4#4R?;0>RWf:RXP<PA123>RYC@/1>RZ11Y>#470DRY,3GX40P011E>/9?132YX40P0P412D3#4,9Z%4290ZD'3X40PIPKP=PLPVPCPAP9P>D5R9/L>%69%6>f=R9PVPAPBP>D5RB/1>RZ#6[[f<R3PXPAP@P>D5/g>A>0>5R@#f12>Z1=B>'9,3B[1dB>1;5>f>RBP3PAPDP>D5R3/=>RZ#61;Z>'K[1_3>1;>5f?R3P9PAP<P>D5R</=>RZ,;>1JZ5'K[1\<>f@R<PBPAPCP>D5RB/1>=>05\@1[B>fARBP3PAPXP>D5RX/=>/3X\@11X>P0fBP<PAPVP>D5/=>P0PJPMP01H04P1PNCFPO17;:,D09<0Q1D0:,7;9<0Q'B,CPPTPRb6b9b:X10X20X301214#4,92%449021'3^10^20^30P2P9PBP4O3b5bHbGbAb@b?b>b0b7b8bB11U>PIPKP=PLPJPMPHPOPPP6P7P7P81E05,BS,CPEYPTPRb6b9b:g01KB\@P2b5b7b8R@9^4>EG11W>PEP?P>P@CXEGA0CFUP2E`b0PDP2EGW0XF0P1P2O2n2001000000121100000W0XD0XE0X=0XC0o"). Qed.

(* [comment removed for export] *)
Theorem popfree_loop_run : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i < n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
  (forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 4 * (n - i))%Z ->
     RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * n + d)) m = true) ->
  exists regs',
    msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                (mkst regs' (Z_to_bv 64 (p + 32)) (pf_mem mem e c s i (Z.to_nat (n - i))) rom)
    /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
    /\ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "p'0h01rh15regs'h24__x1h34__x2h44__x3h51Hh64__p1h74__p2h83H22h93Hk0h:7__arithh;4__ffh<7__sat23h=7__sat24h>8__varmaph?5__with@1bhA1xi001xhB3z22hC4__x4hD4cstrhE4Hkz0hF2HkhG1zhH1yhI2H0hJ2H1hK2H2hL2H3hM2HahN1mhO1ni011nhP1qhQ3H10hR3H11hS3H12hT3H19hU3H21hV2HchW3HcshX2HehY2HihZ3Hinh[2Hjh\3Hkzh]3Hmsh^3Hneh_2Hsh`3Hwrha3R10hb3R11hc3R12hd3R14he3R15hf3R19hg3R21hh2Rohi7__sat25hj1chk1dhl1ehm2e0hn1iho1jhp1khq3memhr2n0hs4regsht3romhu1sp%0p%1p&0p;1p;2p;3p;4p;6p;5p;<p;Fp;7p;8p;Bp-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p710P1p8p101Z6p4p710P1p8p10022p4p710P1p8g004Dj1TTg004ij1iTg005Nk10>Tg00OXk108Tg01[=k20wTg0031k10hTg005lj1ETg01]Fj27Tg00m7j21Tg008[j32k10TTg00n:j2?Tg00S2j2:Tg00WiS00j2FTg01R7k20gTg00RRR1j19Tg00SOR2j24Tg00m]j20Tg01[ik40ITg018=R3j1PTg00:Hj2MTg02Hfj6QTg01icj5<Tg0120j1vTg01^8S01j2ITg00U]k20vTg00V@k30uTg00dcm<04Tg00V]j4WTg01T;k20eTg01Tck30dTg011Ok20PTg00Slj2VTg012Ij2UTg012ik20OTg00nVS02j25Tg013Pk20NTg0147k20LTg014]k20KTg01:Zj2}Tg019[k10cTg01:9k20bTg00Q\R4j1;Tg01Ack30?Tg01C5j2{Tg00XEk10aTg01Caj3zTg00Xek10`Tg00YEk202Tg015Ck10_Tg00Yck10^Tg00ZAk10]Tg00Zlk20<Tg00[Oj2oTg015ak10\Tg00^Gk20[Tg00^ik20ZTg00_Uk30YTg00`4k40GTg00oWk10FTg00WDj1wTg00\Uj3yTg00`fk409Tg01SXk40XTP0j6YTg00\2j3~Tg01=Ik20WTg016ak60DTg02b]mF0VTg010^k20tTg02=Gj4hTg02=bk40sTg006Jk30rTg01kIk303Tg01@lk20pTg00d>m<0ATg0199k20nTg01AIk20mTg01BLk30lTg01?Fk40jTg01EIk30kTg00]8k40@Tg00]ck70QTg01DAk70iTg01?dk60oTg01Dek70fTg01@Hk80BTg00cXmB0qTf1R0f0R5g00??40rp=kf3R6f2R7/70;25p==g00KER8/F5p=>1070/:5,46p=N1:05,07p=|1405,17p>0Jg00@eR9g00AER:725p>0=g00eHR;?205p=Zf4R<1:70,46/V5'1p=Rf6R=f5R>1:70,06,1<32/55p=XA2=><A2670/55'5p=8117092<6/55p=c1:70,46,1<92=>/55p=Sf7R?P=P>P<P6P7D<<030/55p=J20p85p=Cg00<TR@?258p=DA2@05p=61M@5p=@P@P;P@P@P3P<P1P6g01H@P7P0P5N<0Ap=r20n85p=t1?85p=HA2@67,5<1F08/55+0mp=[1F58p>0MB0l@05p=]P@P7P0P5H0jp=bB0k@05p=eP@P0g01G2P5H0@p=nP0g00i\R3g00j;RAPAg00j[RBP5g00kbRCK0Qp=GP7P3PAPAPBP@P0g00k;P5H0@PCK0Qp=OP7P3PAPAPBP0P5K0ip=fP@P0g01GYP5H0@p=mP0P3PAPAPBP5J0op>0;P7P3PAPAPBP0P5K0fp>0:P6P3PAPAPBP7P0P5L0Bp>0HP=P3PAPAPBP>P<P6P3PAPAPBP7P0P5L0BL0Bp=a1:05,47p=j11059267p>0117059267p=B1505,57p=^1505,57,56,5<p=\P>P<P6P7P0D<:03?=/55p>00P;P;P@P@P4P1P1P6g00gmP7P01M@5N<0Ap=`P;P@P@P@P1P1P>P<P6P7P0P5N<0Ap=lP@P@P5P0P7P6P<P>P=P?f8R4f9R3N<04p=qP;P@P5P1P0P7P6P<P>P=P?P4N<04p=uP@P@P@P@P@P@P2P5P0P7P2P6P<P>P=P?P4P3NB0qp>0E%90/:5p>051V70,1692></55p=s1470,1692></55p>07P>P<P6P7P0D<>03=5p>0U%90/:5,47,16p=_1767170552<p=L17=>1:70,06,1<52?/55p=A1767=2<0/55p=3P>P<P6P7P0%;5EQp=dP<P6P7P0P5D<:03=>p>0S%97/:0,46/V5,1<p=K1070/:5p>0R1470/V5p>0C1:05,07,16p=xA2670/55p=p1:05,47,16p>06%90/:5,47p=gg00>ZR2#TRC#iRD$0>RE%TCS03#TS04#TRF#TRG#TRH$0>RI$08RJ+0wRKQ04$0>$08$0h\JS05Q05%TDRL#E,kES06,7?S0711I<RM52J%iD#E,kES08,74S09=2JM%i2RD#T#T#E,kERN,73S0:=2JMPJf:RO%iL#E,kERLPMC=PJf;RPQ03#i#i#E,kERQPMC=%>31?O=Q03#ERM/:?/FO%ECRR%EHRH+0gS0;,?P%>PS0<Q0<f=RSPPf?S0=f<S0>CNQ0;'?%>0%90S0?,47Q0=fCRT'0RU,:M'Fp,4segsRVfFRWf@S0@9|TM>0JI6P7H0I$0=[[^N;^k@fAS0A,0S#PP;1M;5f>S0BfBRX'0#P/Z5P;Q0@fDRY'0RZ#PR[/Z5PVp,2fxR\fIR]p,1pR^,1IR_fHR`fGRaP\P5%EG:0JI^R^P`fERGPYPTPWP7EQPaD<PJQ06,75Rb11IXRcPJQ08,75Rd11IGS0CPJ175NRePIPY10XWRfPTPJ175LRgPIPTPJ175QRhPcPJ%iDRc#T#E,kERi,75RjPIPY%E2Rk,0fPT%EFRFDRPJ%ic#E,kERl,75RmPIPGPMPX&08EREQ0692E5#vRnA2E0N#vRoA2E7i#vRpA2E6l#vRq17><RrfNRs/7<S0D52J[[[[]0FXF8DcFSF8GJX1K,IK]FP0%PUg00hQRU52;A2;[U%CZ#DRtP;P@&0T;S0EP1&0T@R1Q0?%95S0F'61Z0520v0540uXH;XA;S0GP[%C5XA@S0HPZO1P5XA@R[Q0HPZPZ%@ZDrPUP81M@8N<04P5CWPtQ0A/0GRt#t%Ht%CtRZPtPt%DZD[%CfS0IP@20eRHS0J%HR%>HQ0;#H[[S0K%>RRZg01YZRuB0dRH0UWMS0LQ0;#>\u^MZS0MPa10G]RZPkPWCN00PF%DFS0N#vS0OP`fJRu,0WRHPkPaCNRR1VRFS0P,:F1URF'4'6[20ORF%HFS0QP]fKRR,0aS0RPkP`CNRv/UFRw#>1?wF'5[20NvF1?F8S0SPufLRv,0`S0TPkP]CNRw/UFRx,?F&0Mx'5[20LwFQ0NPRfMRw,0]S0UPkPuCNRx/VF#D[20KxFQ0NPv10usS0VPkPRCNRx/UF/6x[1VxFS0WP@PwfORx,0RS0XPkPvCN/UFP@p-0Ryg00i0Rz1}@UR{&0c2-0b@S0Y%;UR|#;S0Z,}@S0[60?@S0\1}@|']']g01HmS0]'{&0azS0^3z&0`zS0_202@0&0_@S0`202@6S0a7b77b6&0^@S0b&0]@R|20<@8R}1o@DRD1o@CRC'eR~'n,G|1o@cRc=O|~5f|1m~},G|20;|>S0c5f|60:|&0\ARAP|AO|c}PAP|1nCD,G|PA20;|=S0dH0HFa20[|BS0eP5P71M9:S0f20Z57$0=dB0Y@80S0gH0GS0hb;b>b?X2@X3@X4@X6yW71005R8#HP7P8P8P6D[%D6S0i1?76P?[[[^2@^3@^4@^6y^7yP5PVP\fUR8P_fTR:fSR9D<S0jP\P5P^P:fQRBfPRcPxfRR~PUEQP911IsS0k92JbS0l11IBS0m92JdS0nPJPePI10s~S0o=jcxH01S0p11IxS0q92JgS0rQ0k92JhS0sPJPjPIP6H01PJPmPIPBPMPsPJPrfZRUP<CB\q\p\o\n^0EFXS0t3^D\L00X1K,IK%DOPOPwPBPPQ0>PWO8b:b0bPbLbKbJbIb5b<b=bBb8b9WF%Pt%;5'Z%;0S0u#9Rt/6fS0vQ0?/4kS0w/6fP1P[P11605$0FXH@XA@S0xPtQ0wP[P[Q0F#@XA;S0FQ0uQ0w145kXA@RtP0Q0?Q0?C`S0yElPfPf%@fS0zM:q%PfS0{Q0u'ZQ0IQ0w'6S0wQ0EP1Q0GQ0{Q0HPfO1P[Q0HPfPfQ0zDrQ0uPtQ0?O1Q0yM9uP5CWQ0w%w7%97S0w#>10Y`Rf#t%Hf%CfS0yPfPfQ0y#DD[%CZP@Q0JQ0KQ0LQ0MQ0Z#;S0Z,}@S0?Q0\/]{']Q0]'{Q0YQ0?60?@Q0[/]{']Q0]'{Q0^5zz5zzQ0_202@<Q0`7b<Q0`7b7Q0a7b0S0[Q0bP|Q0dQ04,o@S041eCDS0\5O|5f|Q0\/m},G|20;|?S0u5f|60:|PAP|Q041o@2R220<@kS0z5y@S0{5O|PAP|1nDC,G|PAQ0{Q0\5O|H0HFaQ0eQ0hb;b>b?X2@X3@X4@XC@X6yX7yP<P61007S0{Q0{P>D[140kS0I,6<1?<6S0|146kS0}10<>S0~'6[[[^2@^3@^4@^C@^6y^7yP5Q0iQ0U#HS10P6PwP]%94P<P=PXO9b:b<b=bBb8bDb9H09Q0vP7PuP]P`PaPWPGPYPT%;7S0v#9S11,4aS12,6TQ0w/4kS13,4aS14,6TP1P[P1Q0xPTPT%@TQ12Q14P[P[P[P@P@g01Y61405H0X#@XN@XO@S14PaPa%@aQ11Q13P[P[Q0FQ0vQ13PtP7Q0wQ0wC`ElS0wN:0EM:qQ1110TaS0v'6Q13Q0v'6S12P1P[P1Q0xQ11Q13Q0wQ0vQ0vQ0v#@M:qP5CWQ12%PfS12%;6S0w'ZQ0y%96S13/4kS15'6S16Q0EP1Q0GQ12Q0yP[Q0HPfPf%@fDrQ0wQ15PtP6Q13Q13C`M9uP7CWQ16%w<%9<S16#>%tH%HH%CHS15PHPHQ15#DD[Q0R#CS0yP@Q0JQ0KQ0LQ0MQ0YQ0Z#;S0Z,}@60?@Q0?/]{']Q0]'{Q0^5zzS0YQ0_Q0[Q0bP|Q0dQ041e2CS125O|5f|Q12/m},G|Q0u5f|60:|S0uPAP|Q04Q0z9y@DRf5O|S04PAP|Q129O|fS0dPAP|1nC2,G|S17PAAy@Cf9O|2FaFaQ0eP5P7Q0fQ0gH0Gb;b>b?X2@X3@X4@XC@X6yX7yP<P61050S0gQ0gP>D[S0gQ0},6<S0}14<k1076S0f'6S18Q0|14=k,4>,6<[[[[^2@^3@^4@^C@^6y^7yP5Q0iQ0X#HP6%9OS0XPxPRP<P=P?PYO:b:b<b=bBb8bDb9bEH09PXQ0AQ0@Q0=Q0BPSPPPOP3P4P@Q0vAjW5GQ0;'?XG@P?Q11P5EY1F`51?5Y'5%;<S11#9S0;/6ZQ16/4k/6ZS0vP1P[P1Q0xQ0;P[PtQ16O1S0iO1P[P[Q0FQ11Q0iPtP<Q16Q16C`ElPZPZ%@ZM:qP7CWQ0v%PHS0v%;>S0i'ZQ15%9>RZ/4kS19'6S15Q0EP1Q0GQ0vQ0HPHO1P[Q0HPHPH%@HS0vDrQ0iPtPZO1S1:PtP>PZPZC`S1;M9uP<CWQ15%w=%9=S15#>Q0T#tQ0T#HQ0T#CRZQ0TQ0T%DZD[Q0U#CS0TP@Q0JQ0KQ0LQ0MQ0^Q0_202@7Q0a7b0S1<Q0b20<@MRZ=~@C,e2Q0\Q0z'e9~@Z5y@A~@Zf,e25O|Q0eQ0hb;b>b?X2@X3@X4@A|5M0Q0{/0k7jM147k,:MS0{,05'6^2@^3@^4@P5P3PwPcO3b:b<b=bBb8bDb9bEA|`MGS0\10G0/0k7jMQ0I9|`M'6P@A|]MWS0I10W7/0k,:MRf'4PVPw11I5Q0ZH0I$0=XG@P3PfQ0ZQ0i#9S1=/6HQ19/6HS19P1P[P1Q0xQ1=P[Q1:O1P[P[Q0FQ0iQ1:Q1;ElPHPHQ0vM:qP6CWS0vQ19Q0R#PS1;%;=S1:'ZQ0yQ15/4k'6S0yQ0EP1Q0GQ1;Q0HQ0RO1P[Q0HQ0RQ0RQ0R#@DrQ1:PtQ15O1PtP=Q15Q15C`M9uP>CWS0RQ0y%w?S1;%9?S1=#>S1>Q0U#tS1?Q10Q0TQ0UQ0UQ0T#DD[S0TQ0V#CS0UP@Q0JQ0KQ0LQ0MQ0?,]{Q0]'{-0W{Q0^5zzS0^Q0_Q0aQ0`7b7Q0`7b0Q0bP|Q0cQ175f|PAP|Q03,o@/n2,G|PAQ12Q0z'eS129~@ZRz,m},G|FaQ0eQ0hb;b>b?X2@X3@X4@X6y1?05,561?60S0zQ0f/0k,:MR}#>[[^2@^3@^4@^6yP51F~OP~POPsP3PaO6b:b<b=bBb8bDb9bEQ0Z#9S0f,4fS031:MHR{'F14fMS0`/F{P@P@Q00P[Q001F05$0FXH@XA@Q03Q0`P[P[P[Q14PfPf%@fQ0fPMP[P[Q0FQ0ZPM%@MElN:0EP{P{%@{N<04Q0vQ19Q0RQ0yQ1;Q1>Q1?Q0TQ0UP@Q0JQ0KQ0LQ0MQ0^Q0_Q1<Q0bP|1mDC,G|Q0c5f|PAP|1nD2,G|PAAy@zZ1e2D9~@Z'm,G|FaQ0eQ0hb;b>b?X2@X3@X4@X6y1F70/56Q0z14}M107<,:M'F[[^2@^3@^4@^6yP51?OsP~POPsP3PaO6b:b<b=bBb8bDb9bEH09O4Q0{,0]P5J0Db5W[Xo@NF0VPVP\PRP_PuP]P\P5P^PuPaPWPGP`Q0wEQP]D<PJPb11IYR7PJPd11IaR}PJPePIPWQ0w005GPJPgQ0CPJPhP7PJPjPIQ13=jWGPFPJPmPIPaPMPYPJPrPcP<CB\q\p\o\n^0EFXEsF8J07F8GJX1K,IKQ01PKPVP\PvP_PRPuP\P5P^PRP`PaPWP]Q11EQPuD<PJPbQ0CPJPd11I`R7PJPePIPaQ0;PWPJPg11IWRZPJPhQ0CPJPjPIQ16=jaWPFPJPmPIQ0\17B<S0\92Jr\q\p\o\n^0EDcEsF8FSF8GJX1KPVP\PwP_PvPRP\P5P^PvP]P`PaPuQ0iEQPRD<PJPbPZPJPd11I]R2PJPePIP`PHPaPJPgP}PJPhPZPJPjPIQ0PPJPmPIQ0I17~<S0I92Jr\q\p\o\n^0EDcDcF8FSF8GJX1K,IKP5PVP\PsP_PwPvP\P5P^PwPuP]P`PRQ1:EQPvD<PJPbP}PJPd11IuRZPJPePIP]Q1:005`PJPgP7PJPhP}PJPjPIQ15=j]`PFPJPmPIPuPMPaPJPrP9P<CB\q\p\o\n^0EFXEsF8J07F8GJQ02PVP\PxP_PsPwP\P0P^PsPRPuP]Pv%;?R?EQPwD<K0UPJP0Q06P7PJP0Q0811IRR}PJP0PNPIPuP?P]C_PJP0PLP2PJP0PQP7PJP0PiPIPuQ1=P]PFDRPJP0PlPIPRPMP`PJP=P<P:P<DL\q\p\o\n^0EGAD3D3D3D3D3D3PVP\PBP_PcPxD<R7P\P5P^PcPwPvPRPsP3EdR2PxPJPbPZPJPd11IwR?PJPePIPvQ0VPRPJPgP}PJPhPZPJPjPIQ0WPJPmPIPwPMPuPJPrfVRZP<CB\q\p\o\n^0EFXDcF8FSF8L00X1K,IKP5PVP7P\P6P^P2PxK0SPJP<Q06P}PJP<Q08Q0kPJP<PNPIPw%;OPvC_PJP<PL11IvR2PJP<PQP}PJP<PiPIPwQ0XPvPFDRPJP<PlPIPsPMPRPJP3P<fWR}/7<R6C=\q\p\o\n^0EGAD3D3D3D3D3D3Q02PJP>Q06P2C=PJP>Q08Q0qPJP>PNPIPs%;PPwC_PJP>PLP?PJP>PQP2PJP>PiPIPsPPPwPFDKPJP>PlPIPxPMPvPJPOP<fXRO/7<S0XC=\q\p\o\n^0EGAD3D3D3D3D3PVQ0jP\P5P^P:PBPcPxP~PSEdP9Q0lQ0nQ0pQ0rQ0sPJPjPIQ0o@0Rkx>0CcFH01Q0t3^D\L00X1K,IKP5Q07Q0k52JPJQ0911I~R2PJ174NPIPBQ0B#;PcC_PJP4PL11IcR?PJP4PQQ0qPJP4PiPIPBQ0BPcPFDKPJP4PlPIP~PMPxPJPSP<f[R4P<DL\q\p\o\n^0EGAD3D3D3F8Q02PJP3Q0811I9R7C=PJQ0:PIP~Q0=#;005BPJP3PLQ0mPJP3PQP?PJP3PiPIP~Q0=PBPFDKPJP3PlPIP9PMPcPJQ0BP<f\RcP<DL\q\p\o\n^0EGAD3D3D3J07PVP\fYR?P_POP}P\P5P^POP8P:P9PZQ0AEdP}D<PJPbP2PJPd11I8RHPJPePIP:10~ZRzP9PJPgP7PJPhP2PJPjPIP:PzPkP9CNPFPJPmPIP8PMP~PJPrf^RzP<CB\q\p\o\n^0EFXEsF8FSF8GJX1K,IKP5PJPPQ08PHC=PJQ0>PNPIP8%;XP:C_PJQ0>PL11I:R2PJQ0>PQP7PJQ0>PiPIP8PXP:PFDKPJQ0>PlPIPZPMP9PJQ0AP<f_R7P<DL\q\p\o\n^0EGAD3D3D3D3Q02PJPSPNPIPZ%;TP8C_C=PJPSPLPHPJPSPQP2PJPSPiPIPZPTP8PFDKPJPSPlPIP}PMP:PJPXP<f`RXP<DL\q\p\o\n^0EGAD3D3D3PVP\f]R:P_PcP4P\P5P^PcP?POP}PU%;GR2EQP4D<PJPb11IZRHPJPd11I?RCPJPePIPO10ZUR{P}PJPg11I}RfPJPhPHPJPjPIPOP{PkP}CNPFPJPmPIP?PMPZPJPrfbRZP<CB\q\p\o\n^0EFXEsF8FSF8GJX1K,IKP5PJQ0=PNPIPOP2P}C_C=PJQ0@PL11IOR2PJQ0@PQPfPJQ0@PiPIP?PWPOPFDKPJQ0@PlPIPUPMP}PJPGP<fcRfP<DL\q\p\o\n^0EGAD3D3D3Q02PJQ0APLPCC=PJQ0APQP2PJQ0APiPIPUPaP?PFDKPJQ0APlPIP4PMPOPJPWP<fdRWP<DL\q\p\o\n^0EGAD3D3PVP\faR2P_PXP7P\P5P^PXP:PcP4PzP]EdP7D<PJPb11IURCPJPd11I:PJPePIPc10UzR{P4PJPg11I4RHPJPhPCPJPjPIPcP{PkP4CNPFPJPmPIP:PMPUPJPrffRUP<CB\q\p\o\n^0EFXEsF8FSF8GJX1K,IKP5PJPTPLPHC=PJPYPQPHPJPYPiPIP:PuPcPFDKPJPYPlPIPzPMP4PJP]P<fgR4P<DL\q\p\o\n^0EGAD3D3Q02PJPGPQ11IcC=PJPGPiPIPzPRP:PFDKPJPGPlPIP7PMPcPJPuP<fhRuP<DL\q\p\o\n^0EGAD3PVP\feR:P_PWPfP\P5P^PWP2PXP7PZPwEdPfD<PJPb11IzRYPJPd11I2PJPePIPX10zZRHP7PJPgPIP7PJPhPYPJPjPIPX10HkP7PFDRPJPmPIP2PMPzPJPrfjRHP<CB\q\p\o\n^0EFXF8DcFSF8GJX1K,IKP5PJPaPQPYC=PJP`PiPIP2PsPXPFDKPJP`PlPIPZPMP7PJPwP<fkR`P<DL\q\p\o\n^0EGAD3Q02PJP]PiPIPZPxP2PFDKC=PJP]PlPIPfPMPXPJQ0DflRYP<CB\q\p\o\n^0EGAPVP\fiRaP_PuP4P\P5P^PuP:PWPfPUPBEdP4D<PJPb11IZRTPJPd11I:PJPePIPW10ZUR{PfPJPgPIPfPJPhPTPJPjPIPW10{kPfPFDRPJPmPIP:PMPZPJPrfnR{P<CB\q\p\o\n^0EFXF8DcFSF8GJX1K,IKP5PJPRPiPIPWPBPfPFDKC=PJPvPlPIPUPMPfPJQ0\foRvP<CB\q\p\o\n^0EGAQ02PJPwPlPIP4PMPWCxC=PJQ0IfpRwP<CB\q\p\o\n^0EPVP\fmRRP_PYP`P\P5P^PYPaPuP4PHP8EdP`D<PJPb11IUS0IPJPd11IaRTPJPePIPu10UHRCP4PJPgPIP4PJPhQ0IPJPjPIPu10CkP4PFDRPJPmPIPaPMPUCxRUPJPrfrS0IP<CB\q\p\o\n^0ECpF8DcFSF8GJX1K,IKP5PJPxPlPUC=PJP8P<fsS02P<DL\q\p\o\n^0EPKPVP\PwP_PvP{D<S0\P\P5P^PvPYP`PHPR%;ORUEQRxP{PJPbPTPJPd11IYRdPJPePIP`10aRRePHH06RbPJPg11IHRgPJPhPTPJPjPIP`10ekS0DPHPFDRRjPJPmPIPYPMPaCxRmfuRh/7<RC92Jr\q\p\o\n^0ECpF8F8F8L00X1KPBPJ11IuS0@PVQ0\P\P~P^PxP{K0SRxA2J5TS0\PJP~Q08PdPJP~PNPbPJP~PLPgPJP~PQPTPJP~PiPjPJP~PlPmA2J6C\q\p\o\n^0ES0mD3S0:D3RCD3S0qD3R6D3R~D33^X@JPJ11I`S09A2JTTRrPJP5PdP~Cp5^xX@JPJPIPH%;}S0k#9S07PaH06PxPrA2JddR~A2J5bP6D\X@JPJPTPxPrP~PIP`PUPHC_=2JbS0tPJP5PgQ0qCpD\X@JPJQ0@PxPrP~Q0tA2JggR6Q0\;^CD\X@JPJPIPH%9}RCPaPFDRPxPrP~Q0tPJP5PjQ0:Cp9^6rD\X@JPJPIP`PMPuCxPxPrP~Q0tP6PrPIP`%9ORaPHPFDR=2JjS0tA2J5mQ0mD\D\X@JP@10uYRuPxPrP~PIP`P5PHH06=2JbQ0tA2JmmS0:Q0m'5S0\'59^6rD\XG@Q07/6u14Ck/6uS0tP1P[P1Q0xQ07P[PtPCO1S0xO1P[P[Q0FQ0kQ0xPtP}PCPCC`ElPuPu%@uM:qP8CWQ0t%PeS0t/ZU%Ce14ak'6S0xQ0EP1Q0GQ0tQ0HPeO1P[Q0HPePe%@eDrPUPtPaO1PtPOPaPaC`M9uP}CWQ0x%w?%9?#>10`vR}#t%H}%C}ROP}P}%DOD[10Yw#CP@Agvc{Rc00tF%>c%>FfqRc205zw<0CF#>[[Q0JQ0KQ0LQ0MQ0I?g7c00PFQ0OQ02Q0I7gXRX1VXF,:F1UXF'4'6[20OXFQ0QftRXQ027g2R2/UFR7#>1?7F'5[20N2FQ0SAghZXRX/UFRZ,?F&0MZ'5[20LXFQ0NfvRX?gfhRh/VF#D[20KhFQ0NfwRh?gWXRW/UF/6W[1VWFP@fxRW?g:h/UFP@Q0YQ0_Q0[Q0bP|Q0uPAP|Q04PAP|Q0dPAP|Q17PAQ12=O|DFaFaQ0eQ0hb;b>b?X2@X3@X4@XC@X6yX7yQ0gQ0}Q18Q0|Q0~/0k/6=[[[[^2@^3@^4@^C@^6y^7yP5%DPf|Ry,0W#HPP%94PyPWQ0>Q0BQ0=PcO:b:b0bPbLbKbJbIb5b<b=bibBb8bDb9bE10uk/6CP@Q0DPVP\PcP_PwPvP\P9P^PwPRPYP`P{P?EdPvD<11IRRv=2JvPJPIPY10H{R{P`H06RvPvPJQ09Q09PJPIPYP5P`PFDRPIB0R{k`>0CYFH01PJPIPRPMPHCxRHPHPJQ0XPXP<CB\q\p\o\n^0ECp5^6F85^6GJXG@PxA2JbbRxA2JjjREQ0\'5Rn,5rRo,56Rp'5Rq,5~R<,5rPsPrP<1MJTRTP~Pq1MJdPxPp1MJbP6Po1MJgPrPnPTPEQ0\1MJjQ0:Q0m1MJmP0ChChChChChChChChPaP5J0Db5Q07P8EY17BlP0EY17BiP>EY17BQP3EY17BLPSEY17BNQ0AEYQ08,7BPGEYQ06,7BP]EYH0sWhWeP0P5O2n2001000010121000000W5WdP0P5O2n2001000010121000000W5WfP0P5O2n2011000010121000000W5WgP0P5O2n2011000010121000000W5WcP0P5O2n2011000010121000000W5WbP0P5O2n2011000010121000000W5WaP0P5O2n2011000010121000000W5W]P0P5O2n2011000010121000000W5X1KP0P5O2n2011000010121100000bmb\WFXp;P5O1n0110101020111101P5O1bFbrW`WWW_WVWXW^WZWYWTWUWSWRWQXO@Xu@Xj@Xl@Xn@WtWqWso"). Qed.


(* [comment removed for export] *)

Lemma pf_mem_wbytes : forall k mem e c s i,
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  pf_mem mem e c s i k = wbytes mem (Z_to_bv 64 (e - 4 * (i + Z.of_nat k))) (pf_bytes c s k).
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "p'0h04__x1h14__x2h24__x3h34__x4h44__p1h52L0h67__arithh74cstrh85cstr0h96__sat9h:4__ffh;8__varmaph<5__with=1Hh>3memh?2H0h@6__sat8hA4__x5hB4__x6hC4__p2hD4__x7hE1nhF1zhG2H1hH2H2hI2H3hJ2H4hK2H5hL2H8hM7__sat11hN7__sat12hO1qhP1rhQ2z8hR2H6hS2H7hT7__sat10hU3Ht0hV1xhW4__x8hX4__x9hY5cstr1hZ5heq_jh[5heq_th\6heq_t0h]1oh^1yh_2Hah`4__p3ha5__x10hb5__x11hc1ahd2b1he2b2hf2s0hg3H10hh2H9hi2Hehj3Hgehk4Hge2hl2Hihm2Hjhn2Hkho3Hlthp4Hlt2hq2Hthr1Lhs2Raht7__sat13hu7__sat14hv4basehw1chx1ehy8heq_basehz1ih{1jh|1kh}1mh~1si001si011ti023z10i032z9i041lp%0p%1p%2p&0p&1p;1p;2p;6p;3p;7p;4p;;p;<p;8p;=p;5p;Bp-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p710P1p8p101Z6p4p710P1p8p10022p4p710P1p8g004Dj1uTg005Nk10uTg00OXk100Tg0031k10xTg005lk10MTg00RRR1j12Tg00WiR2j25Tg01R7k20yTg00n:R3j20Tg02Hfk60wk70:Tg00m7j2DTg00P;j3CTg024bk31Mj4eTg02c]k11GTg01W?j24Tg02dTk317Tg00Q<j2TTg00Q\j1UTg00R;j2_Tg02e\k20jTg017]S00k20hTg008[j3;k10tTg00SOR4j28Tg00S2R5j29Tg00oWk10WTg01SXk40vTg00U]k21TTg00V@k31STg00WDj1OTg01T;k21OTg01Tck31LTg00m]j23Tg01<7k20nTg01:Zk20mTg00XEk11>Tg00Xek11:Tg00Yck115Tg00ZAk114Tg00[Ok20sTg00Zlk20\Tg01UGk311Tg015ak110Tg004ik10<Tg00^Gk20~Tg00:Hj2gTg00^ik20}Tg00_Uk30|Tg00`4k40{Tg00`fj4cTg015Ck10zTg02><k20ETg01AIj2lTg00o1k30YTg02VTk60gTg02XEk60fTg02fCk40VTg02\km;0eTP0k604Tg00Slj2=Tg018=R0j1FTg02f_k20ATg012Ij2<Tg010^k20NTg011Ok20CTg0120k11UTg012ik20QTg013Pk20PTg00nVR6j2ATg0147k20OTg014]k20LTg019[k10dTg01:9k20cTg01=Ij2jTg01Elk61QTg00l_R7k20TTg01eak31KTg00dcm<07Tg00V]k40_Tg0105k60pTg00TIk20ZTg018]j4wTg0089j2pk11CTg00UFk20[Tg02gPk71BTg01;Ck81ATg016ak61@Tg02[bk61=Tg02^0m=1<Tg02hUk51;Tg00cXmB0]Tg00d>m<0kTg01<`k319Tg01BLk30GTg01C5k20>Tg01Cak303Tg00YEk218Tg01?Fk40HTg00]8k402Tg00]cj7qTg00\Uk316Tg00\2k31HTg01EIk31ITg01@Hj8aTg01DAk70FTg01?dk61NTg01Dek70aTg01@lk213Tg0199k212Tg01Ack31PTg00KER8f0R9'5p=1f2R:f1R;/89'9p=X%29,8;p=k19;9,3:p>06158:10;9'Ap=Bg00eHR<?;;9p>0;f3R=18;9,9:'3p=Jg00<TR>/g9p=6P<P<P<P>P>P>g00egP1P1P1P5g00fGf5R5f4R?P=P:P;P9NB0]p=yP<P>P>P>P1P1P5P?P=P:P;P9N<0kp>0SP>P>P>P>P>P>P4P9P;P:P4P=P?P5f6R@f7RAf8RBf9RCNB0]p>0RP>P>P2PAP2P@P5P?P=P:P;P9N<07p>0@A;>;9p=7P<P>P9P1P;P:P=P?P5P@PAPBN<07p=dA;<?=P:P;P9H0_p=s1089p>0U19;9,8:p=}20m>9p=SB19>;9p>0=B0G>;9p=?g00i0RDB0G>:;g01HmRE+0><039p>0D218>9p=^P>P:P;P9H0Hp=HP:g00i\RFg00j;RGPGg00j[RHP>P;g01G2RIP9H02g00kbRJFqp=h20s>9p=ZP:PFPGPGPHP>P;g01GYRKP9H02PJFqp=LB16>;9p=@B1H>;9p=IB1I>;9p=MP@PFPGPGPHP5P?P=PFPGPGPHP:P;P9GaGap=RB0G>;9:0G>:p=:20>;E>03D9p>0iP>P>P?P=P:H0HP;P9H0Hp=oP>P;g00k;RLP9H02p=YP>P;PKP9H02p>09P=PFPGPGPHP:PFPGPGPHP;PJFqP9K0Fp=fP=PFPGPGPHP:P;P9Gap=WP?PFPGPGPHP=PFPGPGPHP:PJFqP;P9Gap=|P5PFPGPGPHP?PFPGPGPHP>P=PKP:H02PJFqP;P9Gap=nP>P?P=P:P;P9J04p=bP<P?P=P:P;P9J04p>0815;9,l:p=mP;PFPGPGPHP9J1Np=[P:PFPGPGPHP;P9K0ap>0X13:;/59p={13:;/<9p=z19:;,3=,3?/<9p=r21389p=>P>P<P>P>P0P?P1P=g01H@P:P;P9N<0kp>0521289p=x15;8A;>98'Ap=v108=A;>:;'A/l9p=`18;9,9:,3=,3?p=KA;>98p=~18;99;>:p=P1598p>0110;9,A:p=VB1P>;9p=NB0G>;900>Ep=QB03D;9p>1RP:PFPGPGPHP>P;PLP9H02PJFqp=GP>P;PIP9H02p=]P=PFPGPGPHP:P;PFPGPGPHP9PJFqK0Fp=tP@PFPGPGPHP5PFPGPGPHP?P=P:GaP;P9Gap=i158;/A9p>0bP<P>P7P1P3g01FPP5P?P=P:P;P9N<07p>0`P:PFPGPGPHP;P9K0Fp>0IP5PFPGPGPHP?PFPGPGPHP=P:K0aP;P9Gap>0?A;>98,A;p>0JA;>:;,A=/l9p>0K18:;/89p=E20>:E20>;E>03D9603Dp>0BP5PFPGPGPHP?P=P:PFPGPGPHP;P9K0FGap>0rP?PFPGPGPHP=P:P;PFPGPGPHP9PJFqGap>0^P>P>P2P5P2P?P8P8P=P:P;P9N<07p>1JP>P>P3PAP3P@P5P?P=P:P;P9N<07p>0qP>P?P=P>P:P;P9H0HH0Hp>0oP<P<P<P>P>P>g00fjP1P1P1P4g00gJP5P?P=P:P;P9NB0]p>1FB03D;9:03D:p=\13;9,3:p>1E15;8/A9p>1D20>9Ep>1?P?PFPGPGPHP=PFPGPGPHP:P;K0FP9K0ap>0lg00>ZS01#uS02#uS03#uS04#uS05#u#uRE$0uR4$00S06Q04$0uS07$00R1$0xR3[%19S08Q03$0MR2%2@S097X;/5?Q02$0MS0:&0MERE+0yRJ,05S0;Q06P3PAP@P5P?P=PBJ0w1k=B:06@2,D4AC5?B61MAQ06&1G91449R7?B7Jf:R7:17A@ACA@7,T1g00hQRI#URL#UR0#URK#URM/_7+0;144:RNPCP2P@f;RO#2S0<CJRP+0j10NP15PN+0hQ00144=RPP7P2PAf<RN#2S0=CJRQ'015QPPNPOP7PCPBf=RQP?K0:PN1kBQ:06O2S0>,D4AC7CQP?Ce5;3P9144?S0?Q0>'0P3PQP5O1RPf>RRPQP2P7f?RS#2RTCJ,D4RUACNOSP@Ce9;39X]3P3PQPNP2PC%2RRVCJRW,D4RXACO7RRYP5CePPPYPQPXP51_MRRP144US0@%29S0A'8RU/5JXE<PW1_MS,k9RZ/5JXF>%2PR[,8WS0B/5J192VR\,8WR]/5JP9XV>R^15;9$0WX^>XV>S0CQ0BP]P^P^P^P>P>g01Y618;9H0v#6X}>XE>S0DPWPW%6WP[P\P^P^Q0A#6XV<S0EPPP\PMP2%62S0FPRPV%6VEyRVJ0SN:0RS0GPJPJ%6JS0HL0@1T1YS0IPPQ0I#2RY/7\R[&0t<S0J&0t>S0K%2;S0LQ0A'720;;921T;941SX^<XV<S0MQ0IPY%6YPPP\PVM9dP=DsS0NP[%OSS0O%1TRTf@RV9CQNS0P,T1R\#ORY%2\#1R\Q0:01OER_Q0:$0U%1E&0UJ[[R`Q0:#1Rag01YZRbQ0:@1LE;UW_RE%1J\b^_aRaP61447S0Q#1RbQ0Q/0JRcfBRdfDRe#2S0R9X2SS0S'3RfQ0R7}2S0T/5JPC144NS0U#1Rg144Q/0JRhfFRiPRO1RjP3%S0R020n>2S0V%SLS0W+0=20m>IRI'?RL&1>DRk40DS0X&1:DRD%^:S0Y%^=S0Z7H;S0[&15>Rl&14>RmQ01-0s>RnQ0:-0\>>11>4S0\5hmS0]&10GRoPm20\>8RpQ02#ZRq5LmS0^Po20\>2RrQ01$0<S0_#ZRs,@q'IRt,MnRu1IrsS0`'@S0aQ0\5LmS0bFRS0c20~mHRvP9P:g00@eRwg00AERx'g20}9:=;wxdB0|>8;H0{Rxb:b;b<X0>X1>X2>109JS0d%1:S0eAX2=?S0f,3:S0g192?S0h'8S0i/5JS0j[[^0>^1>^2>P9fIRw#2RyPefGRzfAR{fCR|O5b6b>W?W=P;P9O2n2001000000121000000b@b9b8b7b5Cc144XS0kQ0NP[Q0OPTPYP\P_P`PEPaP6PbPcABffJPCPjP3%UMS0l#SRX%SMR}%SKRK/?L3:00ikPD&0z>RLP:%^?S0mP;Q0ZDoPlPmPmPpQ0_#uS0n#ZR~PoPmPmQ0`,Y~PoPmQ0]PoPmALmtnS0oPoPmQ0^PoPmPm209puQ0\9hmuCfS0^CWFRS0pD|EnPvPxb:b;b<X0>X1>X2>X3>%1=S0q192=S0r,7?10:JAX2?5S0s/5=%15S0tAX2@AS0u,35S0vQ0v;BJ[[[[[^0>^1>^2>^3>P9fERt=CiwS0w,T1S0x#2S0yPyPePzPBP7P{PdP|O9b6b>X?hX=gP;P9O2n2001000000121000000b@b9b8b7b5-0EWS0zDbQ0IP=I08PP144@RPQ0@'0?mUPXE<PW10P9?mZPXF>1445RZ/0WRWQ0B/5ZS0@'l15]ZRU,lWPWQ0@PWPUp-0RU/gW:0YWWP^Q0CQ0BP]Q0GPZPZ%6ZL0@J0gQ0NP[Q0OPTPYP\P_P`PEPaP6PbPc144OR]/0fS0GQ0T;m]PCPjP3PkPDQ0m?H:LS0TQ0Z7H;S0BPlPmQ03#ZS0@,@s,Ir,MqS0{9hmnRWPo1[m@S0|:0XmWCWPvPxb:b;b<X0>X1>X2>X3>X4US0}P;P2P:P=CJS0~,09Q0g,0;/l5[^0>^1>^2>^3>^4US10P9PzP2PePyCJRW192yS11'8S12144VS13'5PyPePzQ13POO6b6b>X?hX=gP;P9O2n2001000000121000000b@b9b8b7b5CcQ0kQ0zDbQ0IP=I08J0fH0VPQPNPOP7PCPRP5K0:PRPQPNPOP7PCP5Q0NP[Q0OPTPYP\P_P`PEPaP6PbPc%1SPCPjP3PkPD%^;S0IPlPmALmpnS0zPoQ0zCWPvPxb:b;b<X0>S0kQ08%1;S14[^0>S08P9PeP|O2b6b>X?hX=gP;P9O2n2001000000120000000b@b9b8b7b5Q0NP[Q0OPTPYP\P_P`PEPaP6PbPcQ0S/5dPCPjP3PkPDQ0[PlPm1@nqS0S,Ir=LmsS15PoQ15CWPvPxb:b;b<X0>X1>X2>S15AX29;/5:AX2;:S16/5=[^0>^1>^2>S17P9PzPyPePdO4b6b>X?hX=gP;P9O2n2001000000120000000b@b9b8b7b5Q0NP[Q0OPTPYP\P_P`PEPaP6PbPc10dJPCPjP3PkPDQ0IPlPmQ0]PoQ0]CWPvPxb:b;b<X0>S0]Q0d10;JS0I[^0>S0dP9PzP{O2b6b>X?hX=gP;P9O2n2001000000120000000b@b9b8b7b5Q0NP[Q0OPTPYP\P_P`PEPaP6PbPcQ0G192SS0O,3d;m]PCPjP3Q0}Q10P9192eQ135{zPyPePzQ13POO6b6b>X?hX=gP;P9O2n2001000000121000000b@b9b8b7b5N;0eJ04WoP9O1Q0>Q0?'5192CS0?,3NRg-0jZ10Zg15gZ+0hQ001927S00,3QRg,0P15gPPSPRPQPNPOPVPAK0:PS1kOV:06R2,D4Q0PPACe5;3P9144AS0P192OS0>,3RS10'0PSP2PN%2{S0}CJRgP>144CS0G/39/=2P>Q0Q?z;2#FP<Az]f2#FR],g<20;9]R]eP]P;Q0UP|P2%2tR],8VP2DrRf#FRPQ0L%>f'7RZQ0JQ0KQ0MP;Q0LQ0L#6PP%>9XV>S0LQ0UP|P2P^P]O1,8VP2DrR]O1P^Q0LPfP]%6]17f]eI05M9dP9DsPZAC|di,T1RZ1_MiR]%2ZRf%2iRP,92Rh'7RjQ0JQ0KQ0MPZPf%6fP]PhPMP2Q0FPiPP%6PEyM9dPODsPj%Oz%2zRj#1%O?%2?S0Q#1Q0x#OS0xQ0y#1S0y144{S0NfHRhP2fJS18,ktP2DrR]#xP]%>]RfP]1v]fC`144dS19PwP2fKRf#2S1:,8iP2DrS1;#>S1<P>P_P`PEPa144tS1=fLS1>P2PwfNS1?#2DKR]00A2%1]%12R]144zS1@Q1?fPS1A,kf8062S1B'3S1C/<2S1D#1[[144iS1EfMS1FQ18fOS1G'k8062S1H'3S1I00N2Q1I#1S1J144hS1KQ1GP2Q1>fQS1L#2S1MDKRZ/=2Rc#1\][Q1C00C2%~2Rb$1US1N192c1<Z2S1O5PZ[20QZ2&0U2Rc144wS1PQ1AP2Q1FfRS1Q#2S1RDKR\/<2S1SQ1S;B2[20P\21028S1TQ18,44S1UQ1LP2Q1?fSS1V#2DKS1W/<2S1X,02Q1X$01S1Y'A[Q1W00O2144fS1ZQ1QP2Q1GfTS1[#2DKS1\/=2#~\bQ1\00L2Q1>,44S1]Q1VP2Q1AfUS1^#2DKS1_/<2S1`Q1_'7\bQ1_/=2S1aP>Q1F,44RYQ1[P2Q1LfVS1b#2S1cDKS1d/<2S1eP>P6Q1?,44S1f#1Q1f/0JQ0efXS1g#2S1h7V:Q1FQ1A,44S0e#1Q1L,44S1i/0JfZS1jQ1QO1P3Q01$0d-0c>RT/N}S1k=:X0Q0W,QI'j01RkPDQ0ZP:%^@S0Z?H5LS1lP;Q0m?H@LDoPlPmPmAhmprS1mPoPmPmQ02$0<R[#u#ZS1n-09p1[mBS1oCfPoPmPmPmPFPGPGPHAGmrpJ1QS1pPo%Z[RHQ0@/@q,Ir'MRG,M~RF1IrnQ1n'@5GmPoPmPmALmpFPoPmPmPpPrPoQ0zEnPoPmPmQ0@,IrS1q,MH,]~PoPmPmPGP~PoPmQ0zPm1]nqCtEnD|FiFiFiPvPxb:b;b<X0>X1>X2>X3>XA>XB>X4U20b@A\cS0zg01KB\bS1rP@P5P2P?P=DKRG192:S1s;PA[%1G%1?\][1925S1t,3@,0AAX2@5={ABQ0t?V5@[[[[[^0>^1>^2>^3>^A>^B>^4UP910@2P@Q1[,44S0tf[S1uQ1gf]S1v#2S1wPAPOPNPQQ1>Q1GO<b6b>WKWJP;P9O2n2001000000121000000bPbObIbHbGb?b=b9bTbMbNbQbLbYb8b7b5b\b[Q14Q0R7V;Q0U/3=/=2RG#617:GRGePGPeP2P{PPCJRP#617?PRPePP144RRP?z52RG#FS0U00TM%>GRF/02Q0UPFP^Q0LPGPG%6GI05PMP2Q0FJ0`ACe|zS0U,T1S0R1_MzS1xQ0R#2RG192jRF'7S1yQ0JQ0KQ0MQ0RPG%6GQ1xPFPMP2Q0FPzPj%6jEyM9dPNDsQ1y%Oh%2hS1y#1Q0xQ0yQ0N?zB2RF#xPF%>FRGPF1vFGC`Q19?zC2#>P>144|S19/37RG00N2%1GQ1=/3N/=2#1\][P_P`PEPaQ1E/3QRG00A2%1GQ1K/3SRG/<2RF#1\][Q1@/3R00C2Q1N1=G2,92=PGF[20QG2Q1P/3VRG/<2RF?BF2\c20PG2Q1TQ1U/3{RG/<2RF,02&01F'A[20OG2Q1Z/3dRG/=2#~\b20LG2Q1]/3|RG/<2/7G\b1=G2P>AzYe2P>P6%1efWS1]#2S1Z,0e10N2Pd%1iQ1j#2S1U,0zP6Q1Q,44S1P#1Q1P/0J10V2Q1LQ0t#1Q1^,44S1@/0Jf^S1KQ1bO1P31?0IS1E>0DKkS1=PDPLP?Q0YP;Q0m?H=LS0N9HL?DoPlPmPmQ1mPoPmQ0|Pm&0<[#ZR[/]rCtPoPmPmPm1[mAPm1Yn[CtQ1oAGmnpS0y60ImPoPmPmQ0_$0<#ZRYP~PoAhmnrEnJ0?FiPvPxb:b;b<X0>X1>X2>X3>X4UXCUX`UAV5?2\cP@P;P?20JA;H0K15?=10=2[[[^0>^1>^2>^3>^4U^CU^`UP9&017S0_&0U7S0x%17S1zP7Q1GQ1g,44PtPSPiQ1VO:b6b>WSWRP;P9O2n2001000000121000000WKWJP;P9O2n2001000000121000000bPbObIbHbGb?b=b9bTbMbNbQbLb8b7b5CcbybZ20T;Mg01XXS1{&009S1|&00;RGP6&00:?;;914=:14=;'7RF[14:;14:9'7&00=?;:;[S1}&00??;=:\FB1K:;9P9n2001000000120000000WeWdWEQ1{Q1|Q1}^eG]d]EP9P4PRQ0h%2=S1{5E5S1|,D4S1}Q1|144SS1~/79XF>PtP2PdPjCJRG13PGRF/=27}2S201<F2RF#FS21#2S22'8S23,7PQ20%>FS24'8S25,7PP>P>Q0KP^Q0K17;9$0WX^>XV>PPPP%6PQ23Q25P^P^P^Q0DQ20Q20Q20#6Q22Q24P^P^Q0EQ21Q24P^Q0LPFPF%6FI05J0SN:0RS22N<07Q2100TMQ24/02S24Q21Q0LPPPtP2P^PjO1,8dP2DrS20O1P^Q0LPFQ20Q20#6Q20,7FeI05PMP2Q0FJ0`P;H0_S20Q24ACtehS26,T1S271_MhS28Q27#2RFQ1y,92S29'7S2:Q0JQ0KQ0MQ27PF%6FQ28Q29PMP2Q0FPhQ1yQ1y#6EyM9dPQDsS29Q2:%OwS27%1yS2;Q189Czi,T1RF#OS2<%2F#1S2=Q1;#xS2>Q1;Q1<Q1;Q1;Q1<'vC`S1<Q19Q18P2Q1>#2S19,8zP2Dr#>S1;P>P_P`PEPaQ1I00A2S2?Q1JQ1O#1\][S1JQ1C00N2S1OQ1C#11=\2RF#1\][S1C20CZ2S2@Q1N192FQ1S5P\[S1S20Q\2S2AQ1XQ1X;B2\cS2BQ1W00P2S2CQ1TQ1\/<2S2D,02Q2D$01'A[S2EQ1\00O2S2FQ1a#~\bS1aQ1_00L2S2GQ1eQ1d'7\bS2HQ1d/=2S2IP>Q1fQ1^P2Q1QQ1ZDKS1Z/<2S1fP>P6Q14Q1h,0;S2JQ0eQ1]Q1[fYS2K'k8062S2LQ1s;ENS2M'7P|Q0qQ1u#2S2N,0?S2OP6Q1V,44S2P#1S2QQ2P/0JS2RQ0tQ1uP2Q1gQ1wCJS2S192@R\;EVRF'7Q1QQ1@#1S2TQ1b,44S2U/0JS2Vf_S2WQ1]O1S2XP31NT0=:KIRZQ1kQ1E5:X1NTKS2YQ1E'?20iZk40B60D}PDQ0mP:Q0ZP;%^AS2Z?H5LS2[?H=LDoPlPmPmQ1mPoPmQ03$0<#ZRZ9Lmp1[mCJ0rS2\PoPmPmQ1pPoPmQ0{,Mn1IrHS2]/@Z'YI0^PoPmPmPm1[m7S2^Pm1Y~ZCtPmALmZpS2_Pm1Y~pCtPoPmPmQ0{PnPoQ0{Q2]'@/@~9GmnEnJ0?FRPvPxb:b;b<X0>X1>X2>X3>XA>XB>XD>X4UXCU20bAB\cS2]Q1rQ0s,3=S0s,3:?P\B[P7PAPB&01BS2`00JAH0KAX25@S2a={?=Q0v192BS2b'8=P?C[[[[^0>^1>^2>^3>^A>^B>^D>^4U^CUP9Q0x1072S2cP7PtPOfb#2S2dQ1vf`S2eQ2K,44S2fPSPVPiQ1[O=b6b>WSWRP;P9O2n2001000000121000000WKWJP;P9O2n2001000000121000000bPbObIbHbGb?b=b9bTbMbNbQbLb8b7b5bUCcQ1},44Q1|Q23#1S2gQ23/0JS2h'AQ25#1S2iQ25/0JS2j'AQ2gQ2hQ2iQ2jP^Q0C1g>8Q23Q25Q22J1JP^10;9$0WX^>XV>S2jQ23Q25Q22PJPJQ0HL0qJ0pQ20Q24Q29Q2:Q27Q2;Q2<Q2=Q2>Q1<Q1;P>P_P`PEPaQ2?Q1JQ1OQ1CQ2@Q1SQ2AQ2BQ2CQ2EQ2FQ1aQ2GQ2HQ2IP>Q1fP>P6Q14Q2JQ2MQ2M;BJP|Q0qQ2OP6Q2QQ2RABFFJQ1QQ2TQ2VQ2XP3Q0l#URF#US0l#SS2X%SFRF,NTS1QQ1E,?}S2R3:Q1kQ0W/?IS0W,?K5:XS2Q,?FQ2Q1NTXS2MQ2R'?<0Bk40BPDQ0TP;Q2[P=Q0ZI0oPlPmQ2\PoPmPmQ1pPoPm1MYuS2\Q1q/@Z'YI0^PoPmPmQ2^AGmHZS0Z60ImPmQ2_Pm1YHpCtPoPmALmuYS2_PoPmQ0\9hmYS2^PoPmQ0oPoPmPmQ1q,@u/@HS2[-09pQ2[Q0\5hmCfS0TCWFRJ0?FRPvPxb:b;b<X0>X1>X2>X3>XA>XB>XD>X4UXCUQ2]Q1rQ0g,3AS2QQ1t;PB[P7P@PBQ2`%~@S2R'AH0KQ0s/5B10CJQ0u/55AX2ABS0u,3@S2`Q0?;E7S2JQ2J;BJ[[[[[[^0>^1>^2>^3>^A>^B>^D>^4U^CUP9Q0xQ2cP7Q2fPtPOQ2dQ1vQ2ePSPVPiQ1[P:Q1uO?b6b>WSWRP;P9O2n2001000000121000000WKWJP;P9O2n2001000000121000000bPbObIbHbGb?b=b9bTbMbNbQbLb8b7b5bUCc+0EDbO4b=Q06Q0r%2:5E?,D47;QQ06Q1}Q06PzPiPtPeP|PhP9K0:Pz1D4@Q26P9Ce5;3WcP3P1P=Q01$0MS01,3j/3?=}e|Q05$0MS05'=-0ZMQ07/D8S07Cw,p1PzPiP2P|Q1yCJS1},D4R8Q26Q1}Q1tQ0Q3ES0Q,D4S1|Ce9;39X]3P3P1Q0hQ1{5EGS1{,D4S2O,44S2T1D4GS2V,44S1['3#FQ0UQ07Cw,p1P1P?Q1yQ01'3/35=}teQ05'=-0ZMQ07CwS1y,p1S2d=;39X]3Q1{Q2dP11448S2],39#FQ26Q07Cw,p15;3XF>PGQ2dP1Q0Q/39#FQ26Q07Cw,p15;3XF>Q21,g<Q21-0;=S21eS2JQ21Q1~Q1}'3/=2R8#61758S1~eS14Q1~%F\S2H00[5S2G%25R89EW\S1a/3WS2F#FS2E+0;%>\S2C/88S2BQ2F#>S2A'7Q0JQ0KQ0MQ2GQ2BQ2HQ2CP^Q0LP\P\%6\I05P5P8%68S2CJ1FQ2EQ2AP^Q0LQ2FQ2FQ2F#6I05M9dP5Q13?zW2S2F#FS2AQ2F#>,78S2EQ0JQ0KQ0MP5P8Q2CQ2AQ0LQ13PzP2P^PyO1,8eP2DrR8O1P^Q0LQ2FP8%68Q2F/78eI05M9dP;DsS2FQ2E20T@MQ09/02S0LP@Q09Q09#6PMP2Q0FJ0`P?H0_S09Q0LAChzf,T1S131_MfS2AQ13#2R8Q1:,92S2C'7S2HQ0JQ0KQ0MQ13P8%68Q2AQ2CPMP2Q0FPfQ1:Q1:#6EyM9dPVDsS1:Q2HQ1>#OS2CQ19#1S19%OCS2A%2C#1S13Q18Q1?5Cf,T1R8#OS2B%28#1S2GQ1H192NQ0<3EQ1H'3R8#xP8%>8S1HP8Q1H,v8C`Q1B192QQ0=3EQ1B'3#>P>192RR8#xP8%>8S1BP8Q1B,v8C`Q0O#>P>Q1X#xQ1XQ1X#>R8Q1XQ1Y00J8C`Q2D#>P>P_P`PEPaQ1Z00A2Q1Z#1Q0eQ2L'3S2L/<2#1\][Q1G,44Q1bP2Q1VQ1hDKS1h00N2Q1h#1Q1iQ1gP2Q1^Q1UDKS1U/=2S1i#1\][Q2L00C2Q1NQ1UQ1i,92Q1U/<2S0e3P[Q1U00Q2Q1PQ2KP2Q1bQ2NDKR8/<2S2NQ2N;B2\c20P82Q1TQ2PQ1jP2Q1]f\S2P#2S1PDKS2D/<2R8,02&018'A[Q2D00O2Q0tQ2S'3R8/=2#~\b20L82Q1@Q2PP2Q2KQ1K#2DKR8/<2/78\b1=82P>Q2UQ1vP2Q1jQ2W#2S2U'8P2DrP>P6Q1F#1Q1FQ2e#2'0Q1F#2S2K,8R/7VPfQ1G#1Q1AfcS1G#2'0P6Q1u,44R8#1108JQ1M,8d/7eQ1jQ1v,44S1v#1Q1K,44/0JfgQ2WO1P3Q0l#US0l#SR8Q1k?:KI7:F1NT8S1MQ1QQ2Y=:}I3:Q0V00=0S1@,?K9:8XQ0V00=IS0tQ03$0d-0c>S03/NK,?8'QS2D'jS1YQ1YQ1k/?I,QFS1XQ1Q1?}IS0O'QS1BQ2XQ0tQ0l#US0l#SS0=,NTQ1k7:FS1H'Q'jS0<Q0<Q2XQ0tQ0l#US0l#SS1SQ1H'?'Q'jS1HQ1HQ1BQ1XQ1kQ03/N0S2@/?IS1C5:FQ0tQ0l#US0l#U#SS1kQ0=Q0V00=KS1O9:F}3:'Q'jQ1QQ1@/?I7:}Q2D'jQ02$0d-0c>S02/N8Q1QQ02/NKQ1C'?9:X}3:Q0:-0n>00=IQ0l#SRKQ1S;:0'Q'jQ0=Q1MQ2YQ2@5:X3:Q0tQ1k?:K0'Q'j;\k3\3\3\3\3\3\40BPDQ2Z?HOLP:%^CS1Y?H5LP;%^BS0<P?%^OP=%^7?H@LDoDoPlPmPmQ1mPoPm1[mQPmQ0n$0<#ZRK/]rCtPoPmPmQ1pPoQ04#ZS041@H~,Ir,MYR~'MQ1n,Ir/@K5GmPoPmPmPmPm1]pKAGm[KCfPm1[mRPm1Y[pCtPoPmPmPmPm1IrZRK,]pAGmnKCfPmPm209KpQ0yCfPoPmPmPmPm1@~K/@q/M~RK,]pAGmsKCfPmPm209KpAGmspCfPoPmPm1Yq[PoPmPmQ1n,YZPoPmPmP~Q04PoQ0S=GmsEnD|D|J0?J0?J0?FiFiPvPxb:b;b<X0>X1>X2>X3>XA>XB>XD>XW>XX>Xa>Xb>X4UXCUAVNO2\cQ1rQ2a:1EBAQ00;PN[PNPOPN20JROC`Q00P=Q00Q00/v=C`Q0u,3CR~Q0>;E5/3~R~P@P~Q2R-1D~C`17@R17QRAX27O={NQ18BCS2R/77[[[[[[[[^0>^1>^2>^3>^A>^B>^D>^W>^X>^a>^b>^4U^CUP9Q0_Q1zP7PtPOQ1]faS1z,44fhfj#2fePwQ1cPzPSPVPiPhQ18Q1AQ1LQ2POEb6b>WSWRP;P9O2n2001000000121000000WKWJP;P9O2n2001000000121000000bPbObIbHbGb?b=bMbNbtbuc02bgc03bhbQbLbYb8b7b5bUb\CcbZb[Q0h#F00[=Q1{/3G#F+0;P<Q1t#F00[?R~P1P5Q01,3y/3@=}itQ05'=-0ZMQ07Cw,p1P1P9Q0wQ07Cw,p15;3XE<P3P1P~Q26Q07CwR~,p1Q2dP1P3&1C1RKPKP~Q1yP3\1/gKPtPePhP5P?P=P:K1BL1AH0VQ0QQ1}'3#FP9J1@b=Q1[Q2JQ21Q14Q1~Q2FQ2EQ09Q0LQ1:Q2HQ2CQ19Q2AQ13Q2BQ2GQ1I/<2Rh#xS1IPh%>hRKPh1vhKC`S0QQ1D#>S1DP>P_P`PEPaQ1W00A2S1yQ1W#1Q1`#1\][S1`Q1\00N2S1WQ1\#1Q2I#1\][S1\Q1_00C2S1_Q1NQ1dQ2I,92Q1e3P[S1NQ1d00Q2S1dQ1fQ1f;B2\cS1fQ1Z00P2S1ZQ1TQ1h/<2R],02&01]'A[S1TQ1h00O2S1hQ2L/=2#~\bS1eQ2L00L2S2LQ0eQ1U'7\bS0eQ1iP>Q2NP>P6%1wS1UQ1P,0wS1PQ2SQ2S;BJPz%1fS2IQ1>Q2U'0RfP6Q1],44Rb#1S1]10bJS2UQ2WP2Q2PQ1z#2S2PCJRb?BbJQ1bQ2f#1R]Q1j,44/0JRKQ1GQ1uO1S1uP3Q0O>0DXkPDQ0YP;Q0mP=Q1lI0oPlPmPmQ1mPoALmp[S1lQ1o60ImPoPmPmQ1pPo1MHu1IrY/@[5GmPoPmPm1Irq,MnS1o,]HPoPmALmuHS0mPoPmQ0\9hmHS0\PoQ0pFRD|FiFiPvPxb:b;b<X0>X1>X2>X3>XA>XB>X4UQ0zQ1rQ0g,35?P\A[Q0r,3:S0r,05Q0s/5@10AJQ0;Q0u/5@%1BPBP2PCP7CJS0uQ0u;BJ[[[[[[[[^0>^1>^2>^3>^A>^B>^4UP9Q2cP7POQ1vff#2S0zQ1zfdS0;PSPVQ1^Q1gP:Q1KQ2WQ2eO?b6b>WSWRP;P9O2n2001000000121000000WKWJP;P9O2n2001000000121000000bPbObIbHbGb?b=b9bTbMbNbQbLbYb8b7b5bUb\bZb[-0EGS2WDbQ2TQ1{Q2JQ21Q14Q1~Q2FQ2EQ09Q0LQ1:Q2HQ2CQ19Q2AQ13Q2BQ2GQ1IQ0QQ1DP>P_P`PEPaQ1yQ1`Q1WQ1\Q1_Q1NQ1dQ1fQ1ZQ1TQ1hQ1eQ2LQ0eQ1iP>Q2NP>P6Q1UQ1PQ2SQ18,92;EyRh?BhJPzQ2IP6Q1]Q2UQ1?,92Q2K5EbR~?B~JQ1bQ1uP3Q0=Q1MQ0V00=}Q1E'?9:FXS1E3:Q2XQ1QQ2MQ03/N}S03Q0W3:3:R},?8&1?}R}Q2X,NTQ1E'QRT;\k40BPDQ2Z?H?LP:PLP;Q0<P5PLP=Q1Y?H@LDoDoS1YPlPmPmQ1mPoQ1l1[mOS1m60ImPoPmPmQ1pPoPmQ2\Q04,Ir/@['YI0^S2\PoPmPmPm1[mNAGmZ[S1pPmPm209[pAGmZpCfS1lI0lPoPmQ0ZPoPmQ0@Q045GmS04PoPmQ2_PoPmQ2^PoPmPmPpPYPoQ0TEnFRFRFRFiPvPxb:b;b<X0>X1>X2>X3>XA>XB>XD>XW>XX>X4UXCU20bC7\cQ1rQ2QQ2b;P7[PNPCP7Q0_00JCH0K17A7RcQ0v/5710OJ%1NQ0uQ0>;ENRp?BpJ[[[\c[[[[^0>^1>^2>^3>^A>^B>^D>^W>^X>^4U^CUP9Q0xQ2cP7PtPOQ1vQ1RQ1VQ0zQ1zQ0;PSPVPiQ1>Q1FQ1gP:P=OCb6b>XSKXR]P;P9O2n2001000000121000000XKfWJP;P9O2n2001000000121000000bPbObIbHbGb?b=b9bTbMbNbQbLbYb8b7b5bUb\bZb[+0ES2cDbPiQ2VQ0UQ2OCeQ0UPiQ2VQ2OQ1xQ2]Q0A'8Rc/5JXE<PGQ28#2Rp,89RZ/5JXF>Q2JQ21Q14Q1~1_MwR[#2Rr,8WRL/5JQ12/5JP^Q0CPLQ12P^P^P^Q0DPWPW%6WPrQ11P^P^Q0EP[Q11PMP2Q0FPwPy%6yEyJ0SN:0RS11PJPJQ0HL0@Q2FQ2EQ09Q0LQ1:Q2HQ2CQ19Q2AQ13Q2BQ2GQ1IQ0QQ1DP>P_P`PEPaQ1yQ1`Q1WQ1\Q1_Q1NQ1dQ1fQ1ZQ1TQ1hQ1eQ2LQ0eQ1iP>Q2NP>P6Q1UQ1PQ2SQ1w7}2Ry/5JPzQ2IP6Q1]Q2UQ2P9}b2Rw/5JQ1bQ1uP3Q0XPDQ0YQ0N7H;R[PlPmQ0mPoQ0cCWPvPxb:b;b<X0>X1>X2>X3>Q16={9=S16Q0IQ0qQ0sQ1t'8/5J[[[^0>^1>^2>^3>P9Q1vQ0zQ1zQ0;Q1gQ1KQ2eO7b6b>XSKXR]P;P9O2n2001000000121000000XKfWJP;P9O2n2001000000121000000bPbObIbHbGb?b=b9bTbMbNbQbLbYb8b7b5bUb\CcbZb[Q1[Q2WDbQ0RPNI08Q1xQ2]Q1|,44Rr'5?VrcXE<PG159r?VrZXF>Q1{Q1}/59Q1}/8p7V9XF>Q2JQ21Q14Q1~Q1a,5WRWQ1a/0LRp'AQ1aQ12'0Rr,AWPWPpPWPr1gUW:0YWWP^Q2jQ1aQ1aQ1a#6PLQ12Q11L0qJ0pQ2FQ2EQ09Q0LQ1:Q2HQ2CQ19Q2AQ13Q2BQ2GQ1IQ0QQ1DP>P_P`PEPaQ1yQ1`Q1WQ1\Q1_Q1NQ1dQ1fQ1ZQ1TQ1hQ1eQ2LQ0eQ1iP>Q2NP>P6Q1UQ1PQ2S/5h?VhyPzQ2IP6Q1]Q2U15b~?V~wQ1bQ1uP3Q1QQ2MQ03/?I3:Q0tQ0=?:80'Q'jQ1O=:XI,QF;\k9\T}PDQ1YPlPmQ2\PoPmPmPmQ1mQ1pQ1lI0lPoPmQ0ZPoPmQ04PoPmPmQ0@/]sPoPmPmQ1o,]YPoPmQ2_PoPmQ2[9LmuQ2[Q0a5hmJ0rD|D|FRFRPvPxb:b;b<X0>X1>X2>X3>XA>XB>XD>XW>XX>X4UQ1rQ0~,3@192A;PC[P7PBPC1vCBH0K17@CRu10A@135\,07Q2`/5OQ2R:06A2RAQ00=EAOR\'5Q0?,8A7V\[[[\u[[[^0>^1>^2>^3>^A>^B>^D>^W>^X>^4UP9Q0xP7PtPOQ1vQ1RQ1VQ0zQ1zQ0;PVPiQ1>Q1FP@Q1^Q1gOAb6b>XSKXR]P;P9O2n2001000000121000000XKfWJP;P9O2n2001000000121000000bPbObIbHbGb?b=b9bTbMbNbQbLbYb8b7b5bUb\CcbZb[Q2TQ2cDbQ1[Q2WDbQ0RPNI08J1=J04PiPtPeP|PdPzQ2OK0:PzPiPtPeP|PdP?P=P{PVPSP:P;N=1<J04PRP9J04b_bqbmc01b{bvWpP9O1Q10Q0P'5P3PVPBO1ReP{PVP2PQ%2dRiCJ,D4RzACSRdPCCe9;39X]3P3PV1D4gR3ACRQ{RfPBCePePfPVP3PB1_M{Re144zRzQ0A'8R]/5JXE<Pg1_Md,k9RK/5JXF>%2eRO,8gR7/5JQ0},92Ru,8gR\/5JP^Q0CP7P\P^P^P^Q0DPgPg%6gPOPuP^P^Q0EPePuPMP2Q0FP{Q0}Q0}#6EyRMJ0SN:0RROPJPJQ0HL0@1T1fRfPe%2fRA/7uRYQ0JQ0KQ0MPfPA%6APePuPMM9dP@DsRMPY%OdRu%1iRiACVS|,T1R1#OR|%21#1R1P_P`PEPaQ0W>0D0kPDP[PlPmPmQ1oPHPoPmQ0|Q0\60ImRHPoQ0bCWEnPvPxb:b;b<X0>X1>X2>X3>X4U192;={9=AV5?JR=Q0j[[^0>^1>^2>^3>^4UP9%1PR2PPPjPdPtP@PQO7b6b@b9b8b7b5Cc1443R3PMPYPuPiP|P1P_P`PEPaQ1=PDP[PlPmQ0mPoPmPHPoPmQ0oPoQ0^CWFRPvPxb:b;b<X0>X1>X2>X3>X4UQ16Q0f/5:Q0sQ0s;BJ[\=[^0>^1>^2>^3>^4UP9P2PPPjPdPtPCPQPVO8b6b@b9b8b7b5-0EgRCDbPfP@I08PeQ0G/0zQ0G7m]XE<PgQ0G/09Q0G7mKXF>144BR4/0gRg1574RK'l15\4R],lgPgPKPgP]1gUg:0YggP^Q0CP7P\POP4P4%64L0@J0gPMPYPuPiP|P1P_P`PEPaPkPDQ0BPlPmQ0`,Mq=LmnRqPoQ0|Q0{Q1q'@=Lmn60XmCWPvPxb:b;b<X0>X1>X2>X3>X4UQ1s={;9RnQ0i=m5;[^0>^1>^2>^3>^4UP910PGRGPjPdPtPPP@O6b6b@b9b8b7b5CcP3PCDbPfP@I08J0fH0VPVPSPRPQPNP{PBK0:P{PVPSPRPQPNPBPMPYPuPiP|P1P_P`PEPaQ0kQ08P9PdP{O2b6b@b9b8b7b5PMPYPuPiP|P1P_P`PEPaQ15Q17P9PtPjPdPVO4b6b@b9b8b7b5PMPYPuPiP|P1P_P`PEPaQ0]Q0dP9PtPSO2b6b@b9b8b7b5PMPYPuPiP|P1P_P`PEPaPkPDQ0[PlPmPqPo1[m5>0XmqCWPvPxb:b;b<X0>X1>X2>X4UQ0r=m?;\n^0>^1>^2>^4UP9PGPdPtPPP@O5b6b@b9b8b7b5N;0eJ04WkP9O1n200110000021110411104bfWjP9O1n200110000021110411104bfbrbsWcI1;WiWnWlXz>X~>Xw>Xx>W>X|<o"). Qed.

Theorem popfree_spec_of_code : popfree_spec segs p.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) ["FPX_1"; "PopFreeLoop"] "p'0h01rh14__x1h24__p1h34__x2h44__x3h57__arithh64__ffh77__sat23h88__varmaph95__with:5regs'h;1Hh<7__sat22h=4__p2h>4__p3h?4__x4h@7__sat24hA1zhB4cstrhC1xi001xhD3H22hE4__x5hF3z22hG3HmshH1mhI1nhJ2HahK4__p4hL7__sat25hM4__x6hN1yhO3H10hP3H11hQ3H12hR3H19hS3H21hT2HchU3HcshV2HdhW3HdmhX2HehY3HinhZ3Hokh[2Hsh\3R10h]3R11h^3R12h_3R14h`3R15ha3R19hb3R21hc2Rohd1che1dhf1ehg2e0hh1ihi3memhj1ohk4regshl1sp%0p&0p;1p;2p;3p;4p;:p;Ep;6p;5p;9p;<p;7p;8p;Bp-1p10000p4p710p9p1000\p4p710g0019R0p4p710R1p8p1001Wp4p710P1p8p101Z6p4p710P1p8p10022p4p710P1p8g004Dj1OTg004ij1WTg005Nk106Tg00OXk102Tg01[=k20{Tg0031k10eTg005lj1@Tg00m7j21Tg01]Fj27Tg008[j39k10vTg00S2R1j24Tg00WiR2j28Tg01R7k20dTg00n:j2MTg00m]j20Tg018=R3j1CTg01[ik40`Tg02iWk10^Tg01T;k20]Tg01Tck30[Tg00XEk10YTg00Xek10XTg00Yck10STg00ZAk10PTg00Zlk203Tg00[Ok20=Tg015ak10OTg00^Gk20NTg00:Hk20?Tg00_Uk30zTg00`4k40ITg00nVS00j23Tg015Ck10qTg01UGk30fTg00RRR4j1GTg00SOR5j25Tg00oWk10ETg00WDk10aTg0199k207Tg01AIj2_Tg00Q\j1hTg01<7k20_Tg01<`k305Tg01:Zk20CTg01EIj3oTg00^ik20ZTg00`fj4vTg01W?j2yTg02><k20BTg019[k10VTg01:9k20UTg01Ack30@Tg02jLm:0TTg02kMmE0RTg02Hfj6bTg01icj5ATg0120j1uTg01^8S01j2NTg00P;j3lTg010^k204Tg00Slj2tTg02lVm90xTg016ak60wTg00dcm<0HTg024bj3~Tg02=Gj4qTg02=bk40oTg02m\k20nTg006Jk30mTg00YEk20iTg00]8j4sTg00]cj7rTg01?dk60hTg01DAj7}Tg01@Hj8|Tg01?Fk40gTg00\2k30jTg01@lk20kTg01SXk40lTg00d>m<0FTg00cXmB0GTg01BLk30KTg01C5k20cTg01Cak30rTg01Dek70bTg00\Uk30sTP0k60tTg01kIj3wTf1R0f0R6g00??40mp=`f3R7f2R8/70;96p=6g00KER9/86p=:1M06,38p=F1080/46,57p=?1406,08,17p==1M96p=Xg00<TR:00i6p=gP8g00i\R;g00j;R<P<g00j[R=P:P0g01GYR>P6Csg00kbR?Frp=KP0P;P<P<P=P6J0hp=[f5R@P;P<P<P=f4RAP;P<P<P=P7P8F}P0P6G|p=VP:P8P0P6H0gp=D20=:6p=jP8P;P<P<P=P:P0g01G2RBP6CsP?Frp=ZB0j:06p=i1406,08p={20k96p=^P:P:g01Y6P6H0lp>0D20?:6p=<P:g00eHRCP:P:P3PAP4P7g01H@P8P0P6N<0Fp>0;PCP:P:P:P4P4P@PAP7P8P0P6N<0Fp>0:P:P:P:P:P:P:P5P6P0P8P5P7PAP@f6R5f7R4f8R3f9RDNB0Gp>09P:P:P2P4P2P5P@PAP7P8P0P6N<0Hp>08A9:06p=I1869p=]A9:69p=p20C:6p=fB0K:06p=Yg00i0R2B0K:80g01Hm+0c<0r6p=SP:P0g00k;P6Csp=nP7P;P<P<P=P8P0P;P<P<P=P6P?FrF}p=mPAP;P<P<P=P7P;P<P<P=P:P8P>P0CsP?FrP6F}p=TP8P;P<P<P=P0P6K0bp=xP8P;P<P<P=P0P6F}p>0\B0s:06p=aP5P;P<P<P=P@PAP7P;P<P<P=P8P0P6G|G|p=\P:PAP7P8P0P6J0tp=eP7P;P<P<P=P8P0P6G|p>0W1506,18p>0Q17069978p=;1080,1799@A/36p>0>1t80,1799@A/36p=HA95@AA9780/36'3p=E1480,57,1A995@/36p=RP5P@PAP7P8DA=w40/36p=J1006,18p>01%C69l80p=UP5P@PAA~780P6DAp=L1406,58,17p=BA9780/36p=QP@PAP7P8P0DA=w56p>001078/40,5A/t6,1@p=P1778=9A0/36p=2Aw5@AA9780/36'3p>0<PAP7P8P0P6DA9w5@p=z175@1480,07,1A594/36p=>118099A7/36p=k1080/06p=c1480,57/t6,1Ap=dAl8069~A7p>0M1078/00/46,5Ap>0AP:P:P:P:P:P:P1P6P0P8P1P7PAP@P5P4P3PDNB0Gp>0y1080/46p>0L1580/t6p>0JP:P0PBP6Csp>0uP0P;P<P<P=P6P?Frp>0pg00>ZR?#OR;#WRB$06R1%O;R>#ORE#OS02#OS03#ORF$06RG$02RH+0{RI&06E$02$0e\HS04PHP5%OBRJ#@,`1S0511GARKC6PHP4%WB#@,`1S06PKC6%W?RL#O#O#@,`1RM,73S07=9HK%WJ#@,`1RJ,7DS08=9HKPHf:RN%W>#W#@,`1ROPKC6%:DS09?FD@%@>RK/45S0:/8D%@;RP%@FRF+0dRQ7FDQ09Q09f;S0;PDf=RRPNC?/MQg00@eRSp,4segsRTf?RUPGPRPKPNC=f>RV,0N,4K#CH0`g00AERW39fARXf@RY&0^TRZPUPVPRf<R[Q0;PNPDP3P4P520]PFR\%XP%:F%XQ[[R]%:PR^g01YZR_B0[PF0UWJRF%:Q\_^J^R^p-0R_&0Y2R`&0X2R2%g0S0<&0S:Ra&0P:RbPb203:9Rc20=:?Rd5KbRe1[b7Rf&0O<R<PeEVS0=20Nb=R=P6P820?SWS0>B0z:90S0?H0IReb6b8b9X1:W2%:6/30%:0S0@[^1:^2_S0AP6fBRg/MVPgP3O3b5b<b7P\P]PFP^P`P2%g8Rh&0q:Ri7D0RjPaPbPb1[bARk%j;R;9ZbdRlP<PlEVP=Peb6b8b9X1:X3:X2_AF8601M08[^1:^3:^2_P6%:gPVPgP3O4b5b<b7P\P]PFP^P`P2PjPaPbPb203:KRj/id=Kb;RlPkP<PlEVP=Peb6b8b9X1:X3:X2_14K6S0B/80/3814K0S0C/88[^1:^3:^2_P61MXQPXPVP4O4b5b<b7P\P]PFP^P`P2Q0<PaPbPbPf203:P>0f:GRP9ZbdRfP<PfEVS0DP=Peb6b8b9X1:X2_1M6QS0E,301M0QRe[^1:^2_S0FP614KVS0G/8XPXP4O3b5b<b7P7P8P0Q0@%G0,5810VgRl,4K'8PTfDRkA{gKURm,1GS0H15m7Rn,1GS0IfCRo,0URp,4KRq#CRrP8Pm10YkRs,4KRt#C#GS0J,56S0K/8QXA:%GrRu,5mRv/8Q%^qRw,5mRx/8QP6XC:Ry1806$0EXN:XC:S0LPvPxPyPyPy1506$0D#<XH:XI:S0MPmPm%<mPuPwPyPy%G6#<XCCS0NPrPwPy%^6XC:S0OPqPq%<qI0;J0:N:09S0PPQPQ%<QL08&0a8Rq%G8S0Q#:Rw2079tS0R%Xt%^tRr/It'3%]t%pr'3'_S0SfERr,0X,4K#^S0TP:P\P]PFP^g00hQRt#hRu#hRz#hR{#hS0U#fR|20_:KS0V%fu605:Ru%f{R{Q0V%fzS0W605:Rz20C:tS0X'Y'Y=S|`3SP2%gAS0Y?D7iS0Z9Dh0S0[PaPbPb1[b5S0\Pb%jLRt%jBRB9o:;,ijS0]'nCmPbPbQ0]Pc1[b4S0^DT5xbP<Pb1[b3S0_>0\bfP<PbPbAKbcBS0`AZbB;P<1ij;S0a9o:dR}/atR~=KbPEVF\P=P6P8Q0>20Z68=9SWdQ0?H0IS0?b6b8b9X1:X3:X4:X?:X2_X=_X>_1007,4KRW,I8,3A%]W/3@'_134e%:@?F@714KAS0>,07S0b/5@S0c/8Q[[[^1:^3:^4:^?:^2_^=_^>_P614KrfHRe'8%p7S0dfIRW,0r,4K#XS0ePWP7PrPePAPVPUO:b5b7b@bFbDbBCvQ0H,yGS0fPqPwP\P]PFP^Q0X,YuS0g,Yz=S{`P2%g7S0h?D8i?D0iPaPbPbPbQ0aPdPfDTS0aP<PbPbPbPc%j>R>AZb>;DTP<PbPbPcP}AZb}PDTF\P=Q0?b6b8b9X1:X3:X4:Q0C/86Q0E'3%:7?F78A{8K7Rf#:?FfQ[[^1:^3:^4:P6fGRfPofFRzP[PRO5b5b<b7bB-0BmS0EDePAPmA{oKYRS/5AS0C,1G,yG,86XA:Pn18S6XA:PqPwP\P]PFP^P`P2Q0h9Dh0S0hPaPbAKbctS0iP<AKb}~H0WP=Q0?b6b8b9X1:X3:X4:%:8A{0K8Rh15h7'8[^1:^3:^4:P6P4PoPzP@O4b5b<b7bBQ0I,yGS0IPqPwP\P]PFP^Q0U#hRh#h#f%fhQ0WQ0g'Y'YQ0X,Y{=S|`3SP2%g@R|?D@i?D8iQ0Z7D0PaPb%jERE9KbcP<Pb1atEQ0]5KbP<PbQ0iP<PbQ0aP<PbPbQ0`Q0^P<PbPbPcP~AZb~PDTEVF\F\P=Q0?b6b8b9X1:X3:X4:X?:XE:X2_%:ARP157@108A,4K'8Q0>/87S0>?F7Q%:4/3DQ0:,0@/54RE#:?FEQ[[\P[[^1:^3:^4:^?:^E:^2_P61Mfo%G5PfP4PoPzP7PAP@P[PRO;b5b<b7bB-0BnRPDeQ0fQ0EDePn%G7RE,5611GSS0:,yGQ0J'5'8XA:PmQ0C/5EQ0K'8XA:Q0Q,5nRn/8v18nxPyQ0LPnPn%<nPvPxQ0PL08PqPwQ0RQ0SQ0TP:P\P]PFP^&0V?-0U:S0T>0@:{Q0WQ0X'YS0S;S`9S{uP2Q0Y?D8i%g59D|77D0PaPbPbQ0_Pb%WLRL#jR|9o:;,ijRi,nBCmPbPbPiPc1[bDS0YDT5xbP<Pb1at>=KbiP<PbPb1[bNAZb|;P<1a~>1a}B5KbEVF\P=Q0?b6b8b9X1:X3:X4:X?:XE:XM:X2_X=_X>_100@,4KR},IA,35%]}/34'_157AS0R1085,4K'8AFN47Q0c/55Q0b/54'8[[[^1:^3:^4:^?:^E:^M:^2_^=_^>_P6%:WQ0dQ0ePWP7%G3PDPrPePAP5PUO<b5b7b@bFbDbBCvQ0fQ0EDeQ0IPPDeN:0TWWWVXHCXe:NE0RPTp,2fxRCPgp,1pS0@,1GRPPXPZPCP6Q0@Q03#@60QGR}PXPUPVPRPY10[YR>#CEbPZDAPHQ05,76R~11G[R|PHQ06,76S0311GUS0IPH176MRiPGPVP>PRPH176JS0E11GRRuPH176OS0fP|PH%OL#@,`1R|,76RwPGPVP>%@?R?PRC?Q02#@R>PH%WL#@,`1RL,76RqPGPU14K[&021R1Q059916#uRxA910M#uRvA918|#uRnA917L#uREPH17@ARmPfPAC;[[[[]0J0>EHFEFRFEGJX:I,NIQ01PIPTPCPoPPPgPZPCP6P}PgPYPUPVPX10RXRS#CEbPZDAPHP~PuPHQ0311GYRhPHPiPGPUPSPVPHQ0E11GVS01PHQ0fPuPHPwPGPUPSP?PVC?P>PHPqPGPY14KRPHPmPePAC;\E\n\v\x^01J0>EHFEFRFEGJX:IPTPCPkPPPoPZPCP6P}PoQ0G:01GXRSAUYUlPZFLPHP~Q01PHPiPGPYPlPUCBPHPwPGPYPlP?PUC?P>PHPqPS17WAS0199Hm\E\n\v\x^01CQEHFEGJX:I,NIP6PTPCPrPPPkPZPCP6P}PkPgPXPYPo%CpEbPZDAPHP~Q0IPHQ0311GgS03PHPiPGPXPpPYPHQ0EPhPHQ0fQ0IPHPwPGPXPpP?PYC?P>PHPqQ0HfJRp/7AS0H99Hm\E\n\v\x^01CQEHFEFRFEGJQ00PTPCPzPPPrPZPCP0P}PrPoPgPXPk%CsEbPZDAK00PHP0Q05PhPHP0Q0611GoRSPHP0PMPGPgPsPXCBPHP0PJ11GXPHP0POPhPHP0P|PGPgPsP?PXP>EPPHP0PLQ0:PHP5PAfKRs/7AC6\E\n\v\x^01D2D2D2D2D2D2D2PTPCPePPPfPZDAS0:PCP6P}PfPGPrPKPgC=Rh10gzRl#CRu9lkoPZFLPHP~Q03PHPiPGPkPlPoPHPwPGPkPlP?PoC?P>PHPqPhfMS03/7AS0I99Hm\E\n\v\x^01CQEHFRK0<X:I,NIP6PTQ0:PCP7P}PfPrPkPoPzPuEbPZFzPHPAQ05PSPHPAQ0611GzRuPHPAPMPGPr10ofRhPkCBPHPAPJ11GkRlPHPAPOPSPHPAP|PGPrPhP?PkP>EPPHPAPLPGPzPKPoPHPDPAfNRh/7AS0:C6\E\n\v\x^01G>D2D2D2D2D2D2Q00PHP@Q05PlC6PHP@Q0611GfS0fPHP@PMPGPz10keRSPrCBPHP@PJ11GrPHP@POPlPHP@P|PGPzPSP?PrP>EPPHP@PLPGPfPKPkPHPNPAfORN/7AC6\E\n\v\x^01G>D2D2D2D2D2PTPCfLRSPPPsPZPCP6P}PsPGPWPKPzC=S0E10zpRl9UefPZFLPHP~PuPHPiPGPePlPfCBPHPwPGPePlP?PfC?P>PHPqQ0EfQS0E/7AS0G99Hm\E\n\v\x^01CQEHFEGJX:I,NIP6PHP4Q05PuC6PHP3Q0611GpS02PHQ07PGPW10fsRuPePHP3PJ11GeS07PHP3POQ0fPHP3P|PGPWPuP?PeP>EPPHP3PLPGPpPKPfPHPRPAfRRu/7AS0fC6\E\n\v\x^01G>D2D2D2FRD2Q00PHPDQ0611GsS0eC6PHPDPMPGPp10eSRlPWCBPHQ08PGPWPHPDPOQ07PHPDP|PGPpPlP?PWP>EPPHPDPLPGPsPKPePHPVPAfSRV/7AC6\E\n\v\x^01G>D2D2DkD2PTPCfPRlPPPNPZPCP6P}PNPGQ03PKPpC=S0710phRp9USsPZFLPHP~Q02PHPiPGPSPpPsCBPHPwPGPSPpP?PsC?P>PHPqQ07fURp/7AS0799Hm\E\n\v\x^01CQEHFEGJX:I,NIP6PHQ0;Q06Q03,1GS06C6PHP[PMPGQ0310sNS0;PSCBPHP[PJ11GSS02PHP[POQ0ePHP[P|PGQ03Q0;P?PSP>EPPHP[PLPGPhPKPsPHPXPAfVR[/7AC6\E\n\v\x^01G>D2D2D2D2Q00PHPRPMPGPh10SlS0;Q03CBC6PHPRPJQ06PHPRPOQ02PHPRP|PGPhQ0;P?Q03P>EPPHPRPLPGPNPKPSPHPgPAfWRg/7AC6\E\n\v\x^01G>D2D2D2PTPCfTRRPPPVPZPCP6P}PVPGQ0EPKPhC=S0;10huS029UlNPZFLPHP~PGPhPHPiPGPlQ02PNCBS06PHPwPGPlQ02P?PNP>EPPHPqQ0;fYRh/7AS0;99Hm\E\n\v\x^01CQFEDkGJX:I,NIP6PHPUPMQ06C6PHPYPJ11GlRUPHPYPO11GNPHPYP|PGQ0EAcNV?PlP>DdPHPYPLPGPuPKPNPHPrPAfZRY/7AC6\E\n\v\x^01G>D2D2D2Q00PHPXPJQ0E,1GC6PHPXPOPUPHPXP|PGPuAclR?Q0EP>DdPHPXPLPGPVPKPlPHPzPAf[Rz/7AC6\E\n\v\x^01G>D2D2PTPCfXRlPPPgPZPCP6P}PgPGPpPKPuC=RX10u[RU9URVPZFLPHP~PGPuPHPiPGPRPUPVPHPwPGPRPUP?PVC?P>PHPqPXPHPmf]RXPAC;\E\n\v\x^01CQEHFRDkGJX:I,NIP6PHPoPJ11GVRJC6PHPkPOPJPHPkP|PGPpAcVg?PRP>DdPHPkPLPGP[PKPVPHQ01f^RJPAC;\E\n\v\x^01G>D2D2Q00PHPrPO11GRC6PHPrP|PGP[AcRl?PpP>DdPHPrPLPGPgPKPRPHQ0Hf_RrPAC;\E\n\v\x^01G>D2PTPCf\RpPPPzPZPCP6P}PzPGPhPKP[C=Ro10[YRU9UlgPZFLPHP~11G[R[PHPiPGPlPUPgCBPHPwPGPlPUP?PgC?P>PHPqPoPHPmfaRoPAC;\E\n\v\x^01CQEHFEGJX:I,NIP6PHPfPOP[C6PHPeP|PGPhAcgz?PlP>DdPHPePLPGPYPKPgPHQ0IfbRgPAC;\E\n\v\x^01G>D2Q00PHPWP|PGPYAclp?PhP>DdC6PHPWPLPGPzPKPlPHQ0:fcRlPAC;\E\n\v\x^01G>PTPCf`RWPPPrPZPCP6P}PrPGPXPKPYC=Rh10YJRe9UpzPZFLPHP~PGPYPHPiPGPpPePzPHPwPGPpPeP?PzP>EPRePHPqPhPHPmfeRhPAC;\E\n\v\x^01FEFRDkGJX:I,NIP6PHPsP|PeC6PHPSPLPGPJPKPzPHQ0GffRzPAC;\E\n\v\x^01G>Q00PHQ03PLPGPrPKPpC=C6PHQ0ffgRpPAC;\E\n\v\x^01PTPCfdRePPPlPZPCP6P}PlPGPoPKPJC=Rs10JgRY9UWrPZFLPHP~PGPJPHPiPGPWPYPrPHPwPGPWPYP?PrC?P>PHPqPsPHPmfiRYPAC;\E\n\v\x^01CQEHFRDkGJX:I,NIP6PHPNPLPsC6PHQ07fjRsPAC;\E\n\v\x^01PIPTPCPpPPPzPZDARNPCP6P}PzPGPePKPoC=R[10ohRO#CRf9llgPZFLPHP~11GoPHPiPGPlPOPgPHPwPGPlPOP?PgC?P>PHPqP[PHPmflPAC;\E\n\v\x^01CQEHFRK0<X:IQ0EQ04PhPlPgPoPe10WeRm#CR[EbQ04PTPNPCPuP}P6PZFzWjQ03Ph%G[S03,5eS04,4KRu:01GlPgPoP[I0MS07P[PhPlPgPoPeP\P]PFP^Pe10gzRNP?PlC?Rq004>S0f%:q%:>RqPzPefhRwP?PhI0ARi/t>#:[[S00P`P2Q0<PaQ0=P=Q0?b6b8b9X1:X2_Q0AP61MwePwPJO3b5b<b7b@18ul%^mRJ,5eR~,4KRU/8lPyQ0LPuPUPyPyPy1406$0D#<XH:XI:PKPK%<KQ04P~PyPyPyQ0MPePe%<eQ03PJPyPyQ0NP[PJPyQ0OPmPm%<mI0;J0:N:09N:0yPlPl%<lL082079m%Xm1IJm'3%]m%pJ'3'_%^ORJP:P\P]PFP^204i>%:i10zsRi@0L?p>0Jw>#:\q[Q0V>05:{Q0S;S`P2Q0[PaPbPbQ0\PbAo:BdR{,n;CmPbPbP{PcQ0^DT5xbP<PbPbPb1ijBPtQ0_DTP<PbPbQ0YAZbdBP<1ad;,ij=KbtEVF\P=Q0?b6b8b9X1:X3:X4:X?:X2_X=_X>_XK_1076Rj,I0,3A%]j/3@'_Q0>/34AFD8@Q0R,4K/8@[[[^1:^3:^4:^?:^2_^=_^>_^K_P6%:s1MYQ%pARQ%XiPzPYPAPsP@PrPWO;b5b7b@bLbFbDCvP\P]PFP^Q0fQ00P`P2Q0<PaQ0DP=Q0?b6b8b9X1:X2_Q0FP614Ke/8pPpPXO3b5b<b7b@N90xJ0wPTPCPzPPPhPZPCQ0EP}Q07PZDAK00%GfRX,5hRW,IoRr15hJRs,IoP:P:&0v:RiPyPi1I06$0EXN:XC:PoPo%<oPWPsPyPyPyQ0MPhPh%<hPXPJPyPyQ0NPfPJPyQ0OPOPO%<OI0;J0:N:09N<0H2079O%XO1IJO'3%]O%pJ'3'_%^NP:P\P]PFP^PpPhPYP?PzI0AR^004>%:^fkR^,0pRF@0L?w>0JY>#:\q[Q0TQ0W60@:Q0X;S`P2Q0hPaPbPb1[b@PbAo:d;Ra,ntCmPbPbPaPcQ0\DT5xbP<PbPbQ0^Pb20u;dCmP<1a;t,nd-0pbF\P=Q0?b6b8b9X1:X3:X4:X2_X=_X>_1060R=,I8,37%]=/3A'_AF580Q0R,I8[[^1:^3:^4:^2_^=_^>_P6%:^PQ%XFPAP^PpP@PoO8b5b7b@bLbFbDCvPr%CNRN#G,5zPTPCPYPPPwPZDARYPCPRP}Q0B:01Gz10lpRr9UheRo5~wPZFzXA:P0PgP6DePTPCPwPPPpPZPCPVP}PpPGPhPKPgC=AlelNPZFLK00PTPYPCPRP}PGPzPKPlC=RK=~woPZFzPHPRQ0511GlC6RlPHPRPMPGPhPrPeCBC6RMPHPRP|PGPhPrP?PeP>EPC6R>PHPRPLPKC6RKPHQ0;fnPAC;\E\n\v\x^01R1'3Rx'3Rv'3Rn'3P6PlPnPSPMPvPkP>PxP3PKP1PAP7CqCqCqCqCqbGb;bGH0oWcW`P0P6O2n2001000010121000000W;W_P0P6O2n2001000010121000000W;WaP0P6O2n2011000010121000000W;WbP0P6O2n2011000010121000000W;W^P0P6O2n2011000010121000000W;W]P0P6O2n2011000010121000000W;W\P0P6O2n2011000010121000000W;WGP0P6O2n2011000010121000000W;X:IP0P6O2n2011000010121100000bgWZWUW[WTWXWYWRWSWQWPWOXI:Xl:Xd:Xf:Xh:WiWkQ0@-0nTeo"). Qed.

End PopFreeLoop.

End FPX_1.

End AsanPopFree.
From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
Module AsanPlan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import PropExec.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.

Module AP.
Include APC.
Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.     (* [comment removed for export] *)
Variable LIMIT : Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive snode : Type :=
| YMunmap      (* [comment removed for export] *)
| YBrk         (* [comment removed for export] *)
| YSetTid.     (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive xnode : Type :=
| XIMemset     (* [comment removed for export] *)
| XIMemcpy     (* [comment removed for export] *)
| XMemset      (* [comment removed for export] *)
| XMemcpy      (* [comment removed for export] *)
| XMemIsZero   (* [comment removed for export] *)
| XEnvScan     (* [comment removed for export] *)
| XPnScan      (* [comment removed for export] *)
| XLayout      (* [comment removed for export] *)
| XIStrncpy    (* [comment removed for export] *)
| XPopFree     (* [comment removed for export] *)
| XSniff.      (* [comment removed for export] *)

Inductive plan : Type :=
| PRun (stops : list Z) (k : plan)           (* [comment removed for export] *)
| PSplit (e : expr) (mid : Z) (k1 k2 : plan) (* [comment removed for export] *)
| PCase2 (e : expr) (mid : Z) (k1 k2 : plan) (* [comment removed for export] *)
| PCaseDisj (b1 b2 : expr) (k1 k2 : plan)  (* [comment removed for export] *)
| PShDisj (b1 n1 b2 n2 : expr) (k : plan)  (* [comment removed for export] *)
| PContra                                    (* [comment removed for export] *)
| PFact (K : kentry) (k : plan)              (* [comment removed for export] *)
| PJoin (b : expr) (off : Z) (n : nat) (k : plan)  (* [comment removed for export] *)
| PForget (ixs : list nat) (k : plan)        (* [comment removed for export] *)
| PDropRange (b : expr) (n : expr) (k : plan) (* [comment removed for export] *)
| PGcKeep (ws : list (expr * expr)) (k : plan) (* [comment removed for export] *)
| PBump (m : nat) (k : plan)                 (* [comment removed for export] *)
| PHavoc (rs : list nat) (k : plan)          (* [comment removed for export] *)
| PHavocBig (K : nat) (k : plan)             (* [comment removed for export] *)
| PFresh (r : nat) (logc : Z) (base : option expr) (k : plan)  (* [comment removed for export] *)
| PSys (y : snode) (k : plan)                (* [comment removed for export] *)
| PMmap (krefused kgranted : plan)           (* [comment removed for export] *)
| PMmapIn (kkept kok kdestroyed : plan)      (* [comment removed for export] *)
| PMprotect (krefused kgranted : plan)       (* [comment removed for export] *)
| PBrk2 (kblocked kgranted : plan)           (* [comment removed for export] *)
| PX (x : xnode) (args : list expr) (k : plan)   (* [comment removed for export] *)
| PExt (id : nat) (args : list expr) (k : plan)  (* [comment removed for export] *)
| PEmit (id : nat) (args : list expr) (k : plan) (* [comment removed for export] *)
| PExt2 (id : nat) (args : list expr) (k1 k2 : plan) (* [comment removed for export] *)
| PLoop (J : nat) (N : expr) (inv : acs) (body k : plan)  (* [comment removed for export] *)
| PNext                                      (* [comment removed for export] *)
| PHandoff (h : nat)                         (* [comment removed for export] *)
| PExit                                      (* [comment removed for export] *)
| PSpin                                      (* [comment removed for export] *)
| PFog (i : nat) (sz : Z) (k : plan)          (* [comment removed for export] *)
| PFogNew (i : nat) (sz : Z) (k : plan)       (* [comment removed for export] *)
| PGhost (b n : expr) (k : plan)              (* [comment removed for export] *)
| PUnvis (b n : expr) (k : plan)              (* [comment removed for export] *)
| PHavocBrk (lo hi : Z) (k : plan)            (* [comment removed for export] *)
| PIntro (lo hi : Z) (k : plan)               (* [comment removed for export] *)
| PDiamond (joinpc : Z) (rs : list nat) (k : plan)  (* [comment removed for export] *)
| PRename (m : list (nat * nat)) (k : plan)   (* [comment removed for export] *)
| PCompact (k : plan)                         (* [comment removed for export] *)
| PVia (j : nat) (js : acs) (lo : nat) (karms k : plan)  (* [comment removed for export] *)
| PMerge (j : nat)                            (* [comment removed for export] *)
| PAbstractCell (b : expr) (n : Z) (k : plan) (* [comment removed for export] *)
| PHavocWords (bs : list expr) (k : plan)    (* [comment removed for export] *)
| PRespell (r : nat) (e : expr) (k : plan)    (* [comment removed for export] *)
| PMmapInH (kkept kok kdestroyed : plan).     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition node_sys (y : snode) (cs : acs) : option acs :=
  match y with
  | YMunmap => node_munmap A cs
  | YBrk => node_brk1 A cs
  | YSetTid => node_settid nx0 cs
  end.

Definition node_x (x : xnode) (args : list expr) (cs : acs) : option acs :=
  match x with
  | XIMemset => summary_fill A nx0 cs (x_imemset A) 256       (* [comment removed for export] *)
  | XMemset => summary_fill A nx0 cs (x_memset A) two64
  | XIMemcpy => summary_copy segs A nx0 cs (x_imemcpy A)
  | XMemcpy => summary_copy segs A nx0 cs (x_memcpy A)
  | XMemIsZero => summary_miz A nx0 cs
  | XEnvScan => node_envscan A cs
  | XPnScan => node_pnscan A nx0 cs
  | XLayout => node_layout cs args
  | XIStrncpy => summary_istrncpy A nx0 cs
  | XPopFree => summary_popfree A nx0 cs args
  | XSniff => summary_sniff segs A nx0 cs
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive cres : Type := COk (s : shape) | CErr (code : Z) (where_ : plan) (cs : acs).

Section Check.
Variable XN : nat -> list expr -> acs -> option acs.                      (* [comment removed for export] *)
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).  (* [comment removed for export] *)
Variable XB : nat -> list expr -> acs -> option (acs * acs).              (* [comment removed for export] *)
Variable XON : xnode -> bool.                                               (* [comment removed for export] *)
Variable HS : nat -> option acs.   (* [comment removed for export] *)
Variable KC : nat.                 (* [comment removed for export] *)
Variable bfuel : nat.              (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition check_all (chk : acs -> plan -> cres) (k : plan) (css : list acs) : cres :=
  match css with
  | [] => CErr 3 k (init_acs_of A)
  | cs0 :: rest =>
      match chk cs0 k with
      | COk s0 =>
          fold_left (fun acc cs => match acc with
                                   | COk s => match chk cs k with
                                              | COk s' => if shape_eqb s s' then COk s else CErr 6 k cs
                                              | err => err
                                              end
                                   | err => err
                                   end) rest (COk s0)
      | err => err
      end
  end.

Fixpoint check (fuel : nat) (lc : option loopctx) (cs : acs) (p : plan) {struct fuel} : cres :=
  match fuel with
  | O => CErr 0 p cs
  | S f =>
  let check_in := check in
  let check (f : nat) := check_in f lc in
  (* [comment removed for export] *)
  let gcb := match lc with Some c => lc_bnd c | None => nx0 end in
  if negb match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end then CErr 9 p cs else
  match p with
  | PRun stops k =>
      match run_block_gc segs IT gcb KC bfuel (stops ++ STOPS A) cs with
      | Some cs' => check f cs' k
      | None => CErr 1 p cs
      end
  | PSplit e mid k1 k2 =>
      if expr_vars_lt nx0 e then
      match erange (kn cs) e with
      | Some (lo, hi) =>
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            match check f (set_kn cs (KRange e lo mid :: kn cs)) k1 with
            | COk s1 =>
                match check f (set_kn cs (KRange e (mid + 1) hi :: kn cs)) k2 with
                | COk s2 => COk (SCase e mid s1 s2)
                | err => err
                end
            | err => err
            end
          else (* [comment removed for export] *)
            if Z.leb hi mid then check f cs k1 else check f cs k2
      | None => CErr 3 p cs
      end
      else CErr 3 p cs
  | PCase2 e mid k1 k2 =>
      match erange (kn cs) e with
      | Some (lo, hi) =>
          if negb (Z.leb lo mid && Z.ltb mid hi)%bool then (if Z.leb hi mid then check f cs k1 else check f cs k2) else
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            let cs1 := set_kn cs (KRange e lo mid :: kn cs) in
            let cs2 := set_kn cs (KRange e (mid + 1) hi :: kn cs) in
            (* [comment removed for export] *)
            if kn_contra (kn cs1) then check f cs2 k2
            else if kn_contra (kn cs2) then check f cs1 k1
            else
            match check f cs1 k1 with
            | COk s1 =>
                match check f cs2 k2 with
                | COk s2 => if shape_eqb s1 s2 then COk s1 else CErr 6 p cs
                | err => err
                end
            | err => err
            end
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
  | PCaseDisj b1 b2 k1 k2 =>
      match node_casedisj cs b1 b2 with
      | Some (csa, csb) =>
          match check f csa k1 with
          | COk s1 => match check f csb k2 with
                      | COk s2 => if shape_eqb s1 s2 then COk s1 else CErr 6 p cs
                      | err => err
                      end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PShDisj b1 n1 b2 n2 k => match node_shdisj A cs b1 n1 b2 n2 with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PContra => if kn_contra (kn cs) then COk SNil else CErr 3 p cs
  | PFact K k => if fact_ok (kn cs) K then check f (add_kn cs [K]) k else CErr 3 p cs
  | PJoin b off n k => match node_join segs cs b off n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PForget ixs k => check f (set_kn cs (drop_ixs ixs 0 (kn cs))) k
  | PDropRange b n k => check f (node_droprange cs b n) k
  | PGcKeep ws k => check f (set_kn cs (kn_keep (kn cs) ws)) k
  | PBump m k => match node_bump cs m with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavoc rs k => match node_havoc nx0 cs rs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocBig K k => match node_havocbig nx0 cs K with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PFresh r logc base k => match node_fresh nx0 cs r logc base with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PSys y k =>
      if is_ecall_at segs cs then
        match node_sys y cs with Some cs' => check f cs' k | None => CErr 3 p cs end
      else CErr 2 p cs
  | PBrk2 ka kb =>
      if is_ecall_at segs cs then
        match node_brk2 A LIMIT cs with
        | Some (csa, csb) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => COk (salt2 sa sb)
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmap ka kb =>
      if is_ecall_at segs cs then
        match node_mmap2 A nx0 LIMIT cs with
        | Some (csa, csb) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => COk (salt2 sa sb)
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmapIn ka kb kc =>
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT false cs with
        | Some (csa, csb, cscs) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => match check_all (check f) kc cscs with
                                    | COk sc => COk (salt2 sa (salt2 sb sc))
                                    | err => err
                                    end
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmapInH ka kb kc =>      (* [comment removed for export] *)
      if is_ecall_at segs cs then
        match node_mmapin A LIMIT true cs with
        | Some (csa, csb, cscs) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => match check_all (check f) kc cscs with
                                    | COk sc => COk (salt2 sa (salt2 sb sc))
                                    | err => err
                                    end
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMprotect ka kb =>
      if is_ecall_at segs cs then
        match node_mprotect2 A LIMIT cs with
        | Some (csa, csb) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => COk (salt2 sa sb)
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PX x args k => if XON x then match node_x x args cs with Some cs' => check f cs' k | None => CErr 3 p cs end else CErr 3 p cs
  | PExt id args k => match XN id args cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PEmit id args k =>
      match XE id args cs with
      | Some (fd, ps, cs') => match check f cs' k with COk s => COk (SEmitP fd ps s) | err => err end
      | None => CErr 3 p cs
      end
  | PExt2 id args k1 k2 =>
      match XB id args cs with
      | Some (csa, csb) =>
          match check f csa k1 with
          | COk sa => match check f csb k2 with COk sb => COk (SAlt2 sa sb) | err => err end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PLoop J N inv body k =>
      match loop_ok nx0 cs J N inv with
      | Some nhi =>
          let lo := S J in let hi := nxt inv in
          if (Z.eqb (pc inv) (pc cs) && entails_h A lo hi cs (inst inv J (ELit 0)))%bool then
            match check_in f (Some (LC (pc cs) (inst inv J (eaddz (EVar J) 1)) lo hi)) (loop_body_state J N nhi inv) body with
            | COk SNext => check f (inst inv J N) k
            | COk _ => CErr 7 p cs
            | err => err
            end
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
  | PNext =>
      match lc with
      | Some (LC h nx lo hi) =>
          if (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool then COk SNext else CErr 3 p cs
      | _ => CErr 8 p cs
      end
  | PHandoff h =>
      match HS h with
      | Some ch => if entails cs ch then COk (SHole h) else CErr 3 p cs
      | None => CErr 4 p cs
      end
  | PExit =>
      if is_ecall_at segs cs then
        match node_exit cs with Some code => COk (SExit code) | None => CErr 3 p cs end
      else CErr 2 p cs
  | PSpin => CErr 2 p cs   (* [comment removed for export] *)
  | PFog i sz k => match node_fog cs i sz with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PFogNew i sz k => match node_fognew cs i sz with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PGhost b n k => match node_ghost LIMIT cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PUnvis b n k => match node_unvis A cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocBrk lo hi k => match node_havocbrk nx0 cs lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PIntro lo hi k => match node_intro nx0 cs lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PRename m k => match node_rename gcb cs m with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PCompact k => match node_compact gcb cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PVia j js lo karms k =>
      if via_ok nx0 cs js lo then
        match check f js k with
        | COk sk => check_in f (Some (JC j js sk (nxt cs) lo)) cs karms
        | err => err
        end
      else CErr 3 p cs
  | PMerge j =>
      match lc with
      | Some (JC j' js sk b lo) =>
          if (Nat.eqb j j' && Z.eqb (pc cs) (pc js) && shape_vars_lt nx0 sk && entails_h A lo (nxt js) cs js)%bool
          then COk sk else CErr 3 p cs
      | _ => CErr 8 p cs
      end
  | PAbstractCell b n k => match node_abstractcell A cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocWords bs k => match node_havocwords nx0 cs bs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PRespell r e k => match node_respell cs r e with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PDiamond joinpc rs k =>
      match branch_probe IT cs with
      | Some e =>
          match erange (kn cs) e with
          | Some (lo, hi) =>
              (* [comment removed for export] *)
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs with
                | Some cs' => if Z.eqb (pc cs') joinpc then check f cs' k else CErr 3 p cs'
                | None => CErr 1 p cs
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs1 with
                | Some ca =>
                    match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs2 with
                    | Some cb =>
                        match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                        | Some csj => check f csj k
                        | None => CErr 3 p ca    (* [comment removed for export] *)
                        end
                    | None => CErr 1 p cs2
                    end
                | None => CErr 1 p cs1
                end
          | None => CErr 3 p cs
          end
      | None => CErr 2 p cs                  (* [comment removed for export] *)
      end
  end
  end.
End Check.

End WithSegs.
End FPX_1.

End AP.

End AsanPlan.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
Module AxSymRun3.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Import AX2. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import AX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX_1. Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vals_ev (vals : list word) : nat -> word :=
  fun n => nth n vals (Z_to_bv 64 0).

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.

Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).

Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.

Definition kentry_vars_lt (b : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
  | KZero a n => saddr_vars_lt b a && expr_vars_lt b n
  | KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KImg _ _ => true
  | KAlign e _ => expr_vars_lt b e
  | KRange e _ _ => expr_vars_lt b e
  | KWr a n => saddr_vars_lt b a && expr_vars_lt b n
  | KDisj a1 n1 a2 n2 => saddr_vars_lt b a1 && expr_vars_lt b n1 && saddr_vars_lt b a2 && expr_vars_lt b n2
  | KFill a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KUnk a n => saddr_vars_lt b a && expr_vars_lt b n
  end.

Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
  match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.

Fixpoint log_vars_lt (b : nat) (log : list sentry) : bool :=
  match log with
  | [] => true
  | SE a _ v :: r => saddr_vars_lt b a && expr_vars_lt b v && log_vars_lt b r
  end.

Definition env_agree (b : nat) (E E' : env) : Prop :=
  (forall n, (n < b)%nat -> ev E n = ev E' n) /\ eb E = eb E'.

Lemma edenot_agree : forall b E E' e,
  env_agree b E E' -> expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof.
  intros b E E' e [Hv Hb]. induction e; cbn [expr_vars_lt edenot]; intros H;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    try reflexivity;
    try (rewrite IHe1, IHe2 by assumption; reflexivity);
    try (rewrite IHe by assumption; reflexivity).
  - apply Nat.ltb_lt in H. apply Hv. exact H.
  - rewrite Hb. reflexivity.
Qed.

Lemma adenot_agree : forall b E E' a,
  env_agree b E E' -> saddr_vars_lt b a = true -> adenot E a = adenot E' a.
Proof.
  intros b E E' a Ha H. unfold adenot. rewrite (edenot_agree b E E' _ Ha H). reflexivity.
Qed.

Lemma regs_ok_agree : forall b E E' sr regs,
  env_agree b E E' -> sr_vars_lt b sr = true -> regs_ok E sr regs -> regs_ok E' sr regs.
Proof.
  intros b E E' sr regs Ha Hsr HR r. rewrite (HR r).
  unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
  assert (Hnth : forall i, expr_vars_lt b (nth i sr (ELit 0)) = true).
  { clear HR r. induction sr as [|e t IH]; intros i.
    - destruct i; reflexivity.
    - cbn [sr_vars_lt] in Hsr. apply andb_prop in Hsr as [He Ht].
      destruct i; [exact He | apply IH; exact Ht]. }
  apply (edenot_agree b); [exact Ha | apply Hnth].
Qed.

Lemma mem_denot_agree : forall b E E' base log,
  env_agree b E E' -> log_vars_lt b log = true -> mem_denot E base log = mem_denot E' base log.
Proof.
  intros b E E' base log Ha. induction log as [|[a w v] r IH]; cbn [log_vars_lt mem_denot]; intros H.
  - reflexivity.
  - apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
    rewrite IH by exact H3. rewrite (adenot_agree b E E' a Ha H1), (edenot_agree b E E' v Ha H2).
    reflexivity.
Qed.

Lemma flat_agree : forall b E E' a n,
  env_agree b E E' -> saddr_vars_lt b a = true -> flat E a n <-> flat E' a n.
Proof.
  intros b E E' a n Ha H. unfold flat, estart.
  rewrite (edenot_agree b E E' (a_base a) Ha H). tauto.
Qed.

Lemma log_flat_agree : forall b E E' log,
  env_agree b E E' -> log_vars_lt b log = true -> log_flat E log -> log_flat E' log.
Proof.
  intros b E E' log Ha. induction log as [|[a w v] r IH]; cbn [log_vars_lt log_flat]; intros H Hl.
  - exact I.
  - apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
    destruct Hl as (Hw & Hf & Hr). split; [exact Hw|]. split.
    + apply (flat_agree b E E' a _ Ha H1). exact Hf.
    + apply IH; assumption.
Qed.

Lemma know_ok_agree : forall segs b E E' base kn,
  env_agree b E E' -> kn_vars_lt b kn = true -> know_ok segs E base kn -> know_ok segs E' base kn.
Proof.
  intros segs b E E' base kn Ha. induction kn as [|K r IH]; cbn [kn_vars_lt]; intros H Hk.
  - constructor.
  - apply andb_prop in H as [HK Hr]. apply Forall_cons_iff in Hk as [Hk1 Hk2].
    constructor; [| apply IH; assumption].
    destruct Ha as [Hv Hb].
    destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2|a n fc|a n]; cbn [kentry_vars_lt kentry_ok] in *;
      [ | | | | rewrite <- (edenot_agree b E E' ae (conj Hv Hb) HK); exact Hk1
              | rewrite <- (edenot_agree b E E' re (conj Hv Hb) HK); exact Hk1
              | apply andb_prop in HK as [HK1 HK2]; unfold flat, estart, elenZ in *;
                rewrite <- (edenot_agree b E E' (a_base wa) (conj Hv Hb) HK1), <- (edenot_agree b E E' wn (conj Hv Hb) HK2); exact Hk1
              | apply andb_prop in HK as [HK HK4]; apply andb_prop in HK as [HK HK3]; apply andb_prop in HK as [HK1 HK2];
                unfold estart, elenZ in *;
                rewrite <- (edenot_agree b E E' (a_base da1) (conj Hv Hb) HK1), <- (edenot_agree b E E' dn1 (conj Hv Hb) HK2),
                        <- (edenot_agree b E E' (a_base da2) (conj Hv Hb) HK3), <- (edenot_agree b E E' dn2 (conj Hv Hb) HK4); exact Hk1
              | | ].
    + apply andb_prop in HK as [H1 H2].
      rewrite <- (adenot_agree b E E' a (conj Hv Hb) H1), <- (edenot_agree b E E' v (conj Hv Hb) H2).
      destruct Hk1 as (A & B & C). split; [exact A|]. split; [|exact C].
      apply (flat_agree b E E' a _ (conj Hv Hb) H1). exact B.
    + apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *. rewrite <- Hb.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as (A & B & C). split; [|split; [exact B | exact C]].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + exact Hk1.
    + (* [comment removed for export] *)
      apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + (* [comment removed for export] *)
      apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
Qed.

(* [comment removed for export] *)
Lemma vals_app_agree : forall vals extra ebs,
  env_agree (length vals) (Env (vals_ev vals) ebs) (Env (vals_ev (vals ++ extra)) ebs).
Proof.
  intros vals extra ebs. split; [|reflexivity]. intros n Hn. cbn [ev]. unfold vals_ev.
  rewrite app_nth1 by exact Hn. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Run.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma st_ok_entry : forall E base rom pc sr kn nx regs,
  regs_ok E sr regs -> know_ok segs E base kn ->
  st_ok segs E base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom).
Proof.
  intros E base rom pc sr kn nx regs HR HK. exists regs. cbn [s_pc s_log s_regs s_know mem_denot].
  split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK].
Qed.

Theorem run_sound : forall fuel stops scr pc sr kn nx ss' scs scr' E base rom regs,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  regs_ok E sr regs -> know_ok segs E base kn ->
  scs_denot segs base E scs ->
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
                        (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' E base rom regs Hex HR HK Hsc.
  eapply sym_exec_ex; [exact Hex | exact Hsc | apply st_ok_entry; assumption].
Qed.

(* [comment removed for export] *)
Lemma eagree_env_agree : forall b E E', eagree b E E' <-> env_agree b E E'.
Proof. intros b E E'. unfold eagree, env_agree. tauto. Qed.

(* [comment removed for export] *)
Lemma st_okX_entry : forall E base rom pc sr kn nx regs,
  regs_ok E sr regs -> know_ok segs E base kn ->
  sr_vars_lt nx sr = true -> kn_vars_lt nx kn = true ->
  forall E', eagree nx E E' -> st_ok segs E' base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom).
Proof.
  intros E base rom pc sr kn nx regs HR HK Hsr Hkn E' Ha. apply eagree_env_agree in Ha.
  apply st_ok_entry.
  - eapply regs_ok_agree; [exact Ha | exact Hsr | exact HR].
  - eapply know_ok_agree; [exact Ha | exact Hkn | exact HK].
Qed.

(* [comment removed for export] *)
Theorem runTX_sound : forall t K fuel stops pc sr kn nx E base rom regs,
  itab_sound segs t ->
  regs_ok E sr regs -> know_ok segs E base kn ->
  sr_vars_lt nx sr = true -> kn_vars_lt nx kn = true ->
  let ss' := sym_execTX segs t K fuel true stops (SS pc sr [] kn nx) in
  exists E' R, env_agree nx E E'
    /\ (nx <= s_next ss')%nat
    /\ regs_ok E' (s_regs ss') R
    /\ log_flat E' (s_log ss')
    /\ know_ok segs E' base (s_know ss')
    /\ msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
                   (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)
    /\ (forall E'', env_agree (s_next ss') E' E'' ->
          st_ok segs E'' base rom ss' (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)).
Proof.
  intros t K fuel stops pc sr kn nx E base rom regs Ht HR HK Hsr Hkn.
  destruct (sym_execTX_ex segs t K fuel true stops (SS pc sr [] kn nx) E base rom _ Ht
              (st_okX_entry E base rom pc sr kn nx regs HR HK Hsr Hkn)) as (E' & R & Ha & Hle & HR' & Hlf & HK' & Hms & HALL).
  exists E', R. split; [apply eagree_env_agree; exact Ha|]. split; [exact Hle|].
  split; [exact HR'|]. split; [exact Hlf|]. split; [exact HK'|]. split; [exact Hms|].
  intros E'' Ha''. apply HALL. apply eagree_env_agree. exact Ha''.
Qed.

(* [comment removed for export] *)
Theorem carry_after : forall E base log kn hints kn' scs hs',
  carry log kn hints = (kn', scs, hs') ->
  log_flat E log -> know_ok segs E base kn -> scs_denot segs base E scs ->
  know_ok segs E (mem_denot E base log) kn'.
Proof. intros. eapply carry_sound; eauto. Qed.

(* [comment removed for export] *)
Lemma reg_val : forall E sr R (r : reg), regs_ok E sr R -> getr R r = edenot E (sr_get sr r).
Proof. intros E sr R r HR. apply HR. Qed.

(* [comment removed for export] *)
Lemma regs_ok_set : forall E sr R (rd : reg) v e,
  regs_ok E sr R -> rd <> 0%bv -> edenot E e = v ->
  regs_ok E (sr_upd sr (ridx rd) e) (regupd R rd v).
Proof.
  intros E sr R rd v e HR Hrd He.
  pose proof (regs_ok_upd E sr R rd v e HR He) as H.
  assert (Hb : bv_eqb rd 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hrd. apply bv_eq. exact Hc. }
  rewrite Hb in H. exact H.
Qed.

End Run.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sr_init : list expr :=
  [ELit 0; ELit 0; EVar 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].

Lemma regs_ok_init : forall (sp : word) rest ebs,
  regs_ok (Env (vals_ev (sp :: rest)) ebs) sr_init
          (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp).
Proof.
  intros sp rest ebs r.
  unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
  - pose proof (ridx_range r) as Hlt.
    rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
    set (n := ridx r) in *. clearbody n.
    do 32 (destruct n as [|n]; [vm_compute in Hr0 |- *; first [discriminate | reflexivity] |]).
    exfalso. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stk_ok (segs : list Segment) (mem : word -> option byte) (sp : word) (K : Z) : Prop :=
  forall (a : word) (n : nat),
    (bv_unsigned sp - K <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp)%Z ->
    store_ok segs mem a n = true.

Lemma stk_ok_vaddi : forall segs mem sp K off n,
  stk_ok segs mem sp K -> (K <= bv_unsigned sp)%Z ->
  (- K <= off)%Z -> (off + Z.of_nat n <= 0)%Z ->
  store_ok segs mem (v_addi sp off) n = true.
Proof.
  intros segs mem sp K off n Hs HK H1 H2. pose proof (u64_range sp).
  apply Hs; unfold v_addi; rewrite u_small by lia; lia.
Qed.

Lemma stk_ok_lit : forall segs mem sp K z n,
  stk_ok segs mem sp K ->
  (bv_unsigned sp - K <= z)%Z -> (z + Z.of_nat n <= bv_unsigned sp)%Z -> (0 <= z)%Z ->
  store_ok segs mem (Z_to_bv 64 z) n = true.
Proof.
  intros segs mem sp K z n Hs H1 H2 H3. pose proof (u64_range sp).
  apply Hs; rewrite u_small by lia; lia.
Qed.

Lemma stk_ok_grows : forall segs mem mem' sp K,
  stk_ok segs mem sp K -> mem_grows mem mem' -> stk_ok segs mem' sp K.
Proof.
  intros segs mem mem' sp K Hs Hg a n H1 H2. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
Qed.

Lemma stk_ok_mem_denot : forall segs E mem log sp K,
  stk_ok segs mem sp K -> stk_ok segs (mem_denot E mem log) sp K.
Proof. intros. eapply stk_ok_grows; [eassumption | apply mem_denot_grows]. Qed.

(* [comment removed for export] *)
Lemma stk_ok_init : forall segs ph sp argv envp uid hw (rdraw : EntryDraw),
  stk_ok segs (wrap_mem ph sp argv envp uid hw rdraw) sp stack_max_size.
Proof.
  intros segs ph sp argv envp uid hw rdraw a n H1 H2.
  apply store_ok_wrap_window; assumption.
Qed.

Lemma kwr_of_stk_ok : forall segs E mem (e : expr) (sp : word) K,
  edenot E e = sp -> stk_ok segs mem sp K -> (0 <= K <= bv_unsigned sp)%Z ->
  kentry_ok segs E mem (KWr (SA e (- K)) (ELit K)).
Proof.
  intros segs E mem e sp K He Hs HK. cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite He.
  pose proof (u64_range sp). rewrite u_small by lia. split; [lia|].
  intros d m Hd Hm. apply Hs; rewrite u_small by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma kword_intro : forall segs E mem (e : expr) (a : word) off w (v : expr) (x : word),
  edenot E e = a -> edenot E v = x -> (1 <= w)%nat -> (w <= 8)%nat ->
  (0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + Z.of_nat w <= 2 ^ 64)%Z ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned a + off)) w = Some (word_to_le_bytes w x) ->
  kentry_ok segs E mem (KWord (SA e off) w v).
Proof.
  intros segs E mem e a off w v x He Hv Hw1 Hw H1 H2 Hr. cbn [kentry_ok]. unfold flat, estart, adenot, v_addi.
  cbn [a_base a_off]. rewrite He, Hv. split; [exact Hw|]. split; [lia | exact Hr].
Qed.

Lemma krange_intro : forall segs E mem (e : expr) lo hi,
  (lo <= bv_unsigned (edenot E e) <= hi)%Z -> kentry_ok segs E mem (KRange e lo hi).
Proof. intros. cbn [kentry_ok]. lia. Qed.

Lemma kalign_intro : forall segs E mem (e : expr) m,
  (0 < m)%Z -> (bv_unsigned (edenot E e) mod m = 0)%Z -> kentry_ok segs E mem (KAlign e m).
Proof. intros. cbn [kentry_ok]. auto. Qed.

Lemma kimg_intro : forall segs E mem lo hi,
  (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z ->
  (forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
  kentry_ok segs E mem (KImg lo hi).
Proof. intros. cbn [kentry_ok]. auto. Qed.

Lemma kzero_intro : forall segs E mem (e : expr) (a : word) off (n : expr) len,
  edenot E e = a -> bv_unsigned (edenot E n) = len ->
  (0 <= bv_unsigned a + off)%Z -> (0 < len)%Z -> (bv_unsigned a + off + len <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < len)%Z -> mem (Z_to_bv 64 (bv_unsigned a + off + i)) = Some (Z_to_bv 8 0)) ->
  kentry_ok segs E mem (KZero (SA e off) n).
Proof.
  intros segs E mem e a off n len He Hn H1 H2 H3 Hz. cbn [kentry_ok]. unfold flat, elenZ, estart.
  cbn [a_base a_off]. rewrite He, Hn. split; [lia | exact Hz].
Qed.

Lemma kblob_intro : forall segs E mem (e : expr) (a : word) off (n : expr) k bs,
  edenot E e = a -> eb E k = bs -> bv_unsigned (edenot E n) = Z.of_nat (length bs) ->
  (0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off < 2 ^ 64)%Z ->
  (bv_unsigned a + off + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < Z.of_nat (length bs))%Z ->
     mem (Z_to_bv 64 (bv_unsigned a + off + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
  kentry_ok segs E mem (KBlob (SA e off) n k).
Proof.
  intros segs E mem e a off n k bs He Hb Hn H1 H1' H2 Hz. cbn [kentry_ok]. unfold flat, elenZ, estart.
  cbn [a_base a_off]. rewrite He, Hn, Hb. split; [lia|]. split; [reflexivity | exact Hz].
Qed.

(* [comment removed for export] *)
Lemma wrap_mem_none_low : forall ph sp argv envp uid hw (rdraw : EntryDraw) (i : Z),
  (0 <= i)%Z -> (i < bv_unsigned sp - stack_max_size)%Z ->
  wrap_mem ph sp argv envp uid hw rdraw (Z_to_bv 64 i) = None.
Proof.
  intros ph sp argv envp uid hw rdraw i H0 Hi. unfold wrap_mem.
  pose proof (u64_range sp) as Hsp.
  assert (Hu : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; unfold stack_max_size in Hi; lia).
  unfold stack_to_mem. rewrite Hu.
  replace (Z.leb (bv_unsigned sp) i) with false by (symmetry; apply Z.leb_gt; unfold stack_max_size in Hi; lia).
  replace (Z.leb (bv_unsigned sp - stack_max_size) i) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ext_val_zx_id : forall n (v : word),
  (bv_unsigned v < 2 ^ (8 * Z.of_nat n))%Z -> ext_val false 0 n v = v.
Proof.
  intros n v Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma ext_val_sx_id : forall n (v : word),
  (1 <= n)%nat -> (bv_unsigned v < 2 ^ (8 * Z.of_nat n - 1))%Z -> ext_val true 0 n v = v.
Proof.
  intros n v Hn Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
  assert (Hp : (2 ^ (8 * Z.of_nat n - 1) * 2 = 2 ^ (8 * Z.of_nat n))%Z).
  { rewrite Z.mul_comm, <- Z.pow_succ_r by lia. f_equal. lia. }
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n)%Z by lia.
  rewrite <- Hp. rewrite Z.div_mul by lia.
  rewrite Z.mod_small by lia. replace (bv_unsigned v + 2 ^ (8 * Z.of_nat n - 1) - 2 ^ (8 * Z.of_nat n - 1))%Z
    with (bv_unsigned v) by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma branch_eq_lit : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_EQ v (Z_to_bv 64 z) = Z.eqb (bv_unsigned v) z.
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_eqb. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_ne_lit : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_NE v (Z_to_bv 64 z) = negb (Z.eqb (bv_unsigned v) z).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_eqb. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_ltu_lit_r : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_LTU v (Z_to_bv 64 z) = Z.ltb (bv_unsigned v) z.
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_ltu_lit_l : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_LTU (Z_to_bv 64 z) v = Z.ltb z (bv_unsigned v).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_geu_lit_r : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_GEU v (Z_to_bv 64 z) = negb (Z.ltb (bv_unsigned v) z).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_geu_lit_l : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_GEU (Z_to_bv 64 z) v = negb (Z.ltb z (bv_unsigned v)).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.
End FPX_1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac split_scs :=
  lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| split_scs]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| split_scs]
  end.

(* [comment removed for export] *)
Ltac ground_mod :=
  repeat match goal with
  | |- context [ (?a mod ?b)%Z ] =>
      lazymatch a with
      | context [bv_unsigned _] => fail
      | _ => lazymatch b with
             | context [bv_unsigned _] => fail
             | _ => let v := eval vm_compute in (a mod b)%Z in change ((a mod b)%Z) with v
             end
      end
  end.

Ltac sc_unfold :=
  unfold sc_denot, flat, estart, elenZ, adenot;
  cbn [a_base a_off edenot ev eb vals_ev nth];
  rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; ground_mod.

(* [comment removed for export] *)
Ltac lit_u :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned _] => fail
      | _ => rewrite (u_small z) by (cbn; lia)
      end
  end.

(* [comment removed for export] *)
Ltac sc_store :=
  match goal with
  | Hs : stk_ok _ _ _ _ |- store_ok _ _ (v_addi _ _) _ = true =>
      apply (stk_ok_vaddi _ _ _ _ _ _ Hs); lia
  | Hs : stk_ok _ _ _ _ |- store_ok _ _ (Z_to_bv 64 _) _ = true =>
      apply (stk_ok_lit _ _ _ _ _ _ Hs); lia
  end.

Ltac sc_auto extra :=
  sc_unfold;
  first [ lia
        | sc_store
        | extra
        | match goal with |- _ /\ _ => repeat split; first [lia | sc_store | extra] end
        | idtac ].

(* [comment removed for export] *)
Ltac sym_run_tac segs fuel stops scr nx HR HK R' HR' Hlf Hms extra :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?regs =>
    lazymatch type of HK with
    | know_ok _ _ ?base ?kn =>
      lazymatch goal with
      | |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in
              assert (Hsc : scs_denot segs base E scs);
              [ split_scs; sc_auto extra
              | destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs
                          (eq_refl _) HR HK Hsc) as (R' & HR' & Hlf & Hms);
                clear Hsc ]
          end
      end
    end
  end.

End AxSymRun3.
Module LibSym.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section FPX. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

Fixpoint itab_of_ranges (rs : list (Z * nat)) (t : itab) : itab :=
  match rs with
  | [] => t
  | (lo, n) :: rs' => itab_of_ranges rs' (mk_itab_fuel segs n lo t)
  end.
Lemma itab_of_ranges_sound : forall rs t, itab_sound segs t -> itab_sound segs (itab_of_ranges rs t).
Proof. induction rs as [|[lo n] rs IH]; intros t Ht; cbn; [exact Ht|]. apply IH. apply mk_itab_fuel_sound. exact Ht. Qed.
Lemma itab_leaf_sound : itab_sound segs PTLeaf.
Proof. intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate. Qed.
Definition itab_of (rs : list (Z * nat)) : itab := itab_of_ranges rs PTLeaf.
Lemma itab_of_sound : forall rs, itab_sound segs (itab_of rs).
Proof. intros rs. apply itab_of_ranges_sound, itab_leaf_sound. Qed.
End WithSegs.

(* [comment removed for export] *)
Definition EnvR (R : bvmap 5 word) : env := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => []).
Lemma EnvR_regs_ok : forall R, regs_ok (EnvR R) sr_id R.
Proof. intros R. apply regs_ok_id. Qed.
Lemma EnvR_ev : forall R n, (n < 32)%nat -> ev (EnvR R) n = getr R (Z_to_bv 5 (Z.of_nat n)).
Proof. intros R n Hn. cbn [ev EnvR]. unfold reg_ev. apply Nat.ltb_lt in Hn. rewrite Hn. reflexivity. Qed.

Lemma u64_of_Z : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

(* [comment removed for export] *)
Definition pres_check (sr' : list expr) (exc : list nat) : bool :=
  forallb (fun i => expr_eqb (nth i sr' (ELit 0)) (EVar i) || existsb (Nat.eqb i) exc)%bool (seq 0 32).

Lemma pres_check_sound : forall sr' exc E E' R R' b,
  pres_check sr' exc = true ->
  regs_ok E sr_id R -> regs_ok E' sr' R' -> env_agree b E E' -> (32 <= b)%nat ->
  forall r : reg, existsb (Nat.eqb (ridx r)) exc = false -> getr R' r = getr R r.
Proof.
  intros sr' exc E E' R R' b Hc HR HR' Hag Hb r Hr.
  rewrite (HR' r), (HR r). unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
  pose proof (ridx_range r) as Hlt.
  unfold pres_check in Hc. rewrite forallb_forall in Hc.
  specialize (Hc (ridx r)). rewrite Hr, orb_false_r in Hc.
  assert (Hin : In (ridx r) (seq 0 32)) by (apply in_seq; lia).
  specialize (Hc Hin). apply expr_eqb_eq in Hc. rewrite Hc.
  assert (Hid : nth (ridx r) sr_id (ELit 0) = EVar (ridx r)).
  { set (n := ridx r) in *. clearbody n. do 32 (destruct n as [|n]; [reflexivity|]). exfalso; lia. }
  rewrite Hid. cbn [edenot]. symmetry. apply (proj1 Hag). lia.
Qed.
End FPX.

End LibSym.
