(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed check_all, node_x, pf_bytes_cell and 17 more; added rz; taken in part from projects/jsoncons/fuzz_ubjson_encoder/proofs/lib/S9/AsanPopFree.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, 163 lines within its lines 55-386. *)
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
Proof. intros c s k. induction k as [|k IH]; cbn [pf_bytes length]; [reflexivity|]. rewrite length_app, length_Z_to_le_bytes, IH. lia. Qed.

Lemma pf_bytes_nth : forall c s k j t,
  (0 <= j < Z.of_nat k)%Z -> (t < 4)%nat ->
  nth (Z.to_nat (4 * j) + t) (pf_bytes c s k) (Z_to_bv 8 0) = nth t (Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16)) (Z_to_bv 8 0).
Proof.
  intros c s k. induction k as [|k IH]; intros j t Hj Ht; [lia|].
  cbn [pf_bytes]. rewrite Nat2Z.inj_succ in *.
  destruct (Z.eq_dec j 0) as [->|Hj0].
  - rewrite app_nth1 by (rewrite length_Z_to_le_bytes; lia). replace (Z.to_nat (4 * 0) + t)%nat with t by lia. f_equal. f_equal. f_equal. lia.
  - rewrite app_nth2 by (rewrite length_Z_to_le_bytes; lia). rewrite length_Z_to_le_bytes.
    replace (Z.to_nat (4 * j) + t - 4)%nat with (Z.to_nat (4 * (j - 1)) + t)%nat by lia.
    rewrite IH by lia. f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma pf_bytes_cell : forall c s k j,
  (0 <= j < Z.of_nat k)%Z ->
  firstn 4 (skipn (Z.to_nat (4 * j)) (pf_bytes c s k)) = Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16).
Proof.
  intros c s k. induction k as [|k IH]; intros j Hj; [lia|].
  cbn [pf_bytes]. rewrite Nat2Z.inj_succ in *.
  destruct (Z.eq_dec j 0) as [->|Hj0].
  - replace (Z.to_nat (4 * 0)) with 0%nat by lia. rewrite skipn_O. rewrite firstn_app, length_Z_to_le_bytes, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite firstn_all2 by (rewrite length_Z_to_le_bytes; lia). f_equal. f_equal. lia.
  - rewrite skipn_app, length_Z_to_le_bytes. rewrite skipn_all2 by (rewrite length_Z_to_le_bytes; lia). cbn [app].
    replace (Z.to_nat (4 * j) - 4)%nat with (Z.to_nat (4 * (j - 1)))%nat by lia.
    rewrite IH by lia. f_equal. f_equal. lia.
Qed.

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
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

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
  intros regs mem rom i e c s n H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs Hok.
  destruct Hp as [Hp0 Hp1].
  (* the values computed by the iteration *)
  assert (V14 : v_srli (Z_to_bv 64 c) (bv_unsigned (4 : bv 6)) = Z_to_bv 64 (c / 16)).
  { unfold v_srli. rewrite u64_of_Z by lia. change (bv_unsigned (4 : bv 6)) with 4%Z.
    rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  assert (V15a : v_xori (Z_to_bv 64 i) (bv_signed (4095 : bv 12)) = Z_to_bv 64 (2 ^ 64 - 1 - i)).
  { unfold v_xori. rewrite u64_of_Z by lia. change (bv_wrap 64 (bv_signed (4095 : bv 12))) with (2 ^ 64 - 1)%Z.
    rewrite AX2S.lxor_ones64 by lia. reflexivity. }
  assert (V10 : v_addi (Z_to_bv 64 i) (bv_signed (1 : bv 12)) = Z_to_bv 64 (i + 1)).
  { change (bv_signed (1 : bv 12)) with 1%Z. apply v_addi_lit. }
  assert (V15b : v_slli (Z_to_bv 64 (2 ^ 64 - 1 - i)) (bv_unsigned (2 : bv 6)) = Z_to_bv 64 (2 ^ 66 - 4 - 4 * i)).
  { unfold v_slli. rewrite u64_of_Z by lia. change (bv_unsigned (2 : bv 6)) with 2%Z.
    rewrite Z.shiftl_mul_pow2 by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal. lia. }
  assert (V15c : v_add (Z_to_bv 64 e) (Z_to_bv 64 (2 ^ 66 - 4 - 4 * i)) = Z_to_bv 64 (e - 4 * (i + 1))).
  { unfold v_add. rewrite u64_of_Z by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
    rewrite Z.add_mod_idemp_r by lia.
    replace (e + (2 ^ 66 - 4 - 4 * i))%Z with ((e - 4 * (i + 1)) + 4 * 2 ^ 64)%Z by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  assert (Vst : v_addi (Z_to_bv 64 (e - 4 * (i + 1))) (bv_signed (0 : bv 12)) = Z_to_bv 64 (e - 4 * (i + 1))).
  { change (bv_signed (0 : bv 12)) with 0%Z. rewrite v_addi_lit. f_equal. lia. }
  assert (V12 : v_add (Z_to_bv 64 c) (Z_to_bv 64 s) = Z_to_bv 64 (c + s)).
  { unfold v_add. rewrite !u64_of_Z by lia. reflexivity. }
  eexists. split.
  - eapply mst_step; [reflexivity | eapply (step_srli segs); [exact HF0 | reflexivity | exact PD0] |].
    red_if. rewrite v_addi_lit, H12, V14.
    eapply mst_step; [reflexivity | eapply (step_xori segs); [exact HF1 | reflexivity | exact PD1] |].
    red_if. rewrite v_addi_lit. replace (p + 4 + 4)%Z with (p + 8)%Z by lia. gr. rewrite H10, V15a.
    eapply mst_step; [reflexivity | eapply (step_addi segs); [exact HF2 | reflexivity | exact PD2] |].
    red_if. rewrite v_addi_lit. replace (p + 8 + 4)%Z with (p + 12)%Z by lia. gr. rewrite H10, V10.
    eapply mst_step; [reflexivity | eapply (step_slli segs); [exact HF3 | reflexivity | exact PD3] |].
    red_if. rewrite v_addi_lit. replace (p + 12 + 4)%Z with (p + 16)%Z by lia. gr. rewrite V15b.
    eapply mst_step; [reflexivity | eapply (step_add segs); [exact HF4 | reflexivity | exact PD4] |].
    red_if. rewrite v_addi_lit. replace (p + 16 + 4)%Z with (p + 20)%Z by lia. gr. rewrite H11, V15c.
    eapply mst_step; [reflexivity | eapply (step_sw_val segs); [exact HF5 | reflexivity | exact PD5 | gr; rewrite Vst; exact Hok] |].
    rewrite v_addi_lit. replace (p + 20 + 4)%Z with (p + 24)%Z by lia. gr. rewrite Vst.
    eapply mst_step; [reflexivity | eapply (step_add segs); [exact HF6 | reflexivity | exact PD6] |].
    red_if. rewrite v_addi_lit. replace (p + 24 + 4)%Z with (p + 28)%Z by lia. gr. rewrite H12, H21, V12.
    destruct (Z.ltb (i + 1) n) eqn:Hlt.
    + eapply mst_step; [reflexivity | eapply (step_bltu_tk segs); [exact HF7 | reflexivity | exact PD7 | ] |].
      { gr. rewrite H19. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. exact Hlt. }
      rewrite btgt_lit. change (bv_signed (8164 : bv 13)) with (-28)%Z.
      replace (p + 28 + -28)%Z with p by lia. apply mst_refl.
    + eapply mst_step; [reflexivity | eapply (step_bltu_ft segs); [exact HF7 | reflexivity | exact PD7 | ] |].
      { gr. rewrite H19. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. exact Hlt. }
      rewrite v_addi_lit. replace (p + 28 + 4)%Z with (p + 32)%Z by lia. apply mst_refl.
  - gr. rewrite H11, H21, H19.
    repeat (split; [reflexivity|]).
    intros r Hr10 Hr12 Hr14 Hr15. rewrite !getr_other by assumption. reflexivity.
Qed.

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
  induction k as [|k IH]; intros regs mem rom i e c s n Hn H10 H11 H12 H21 H19 Hi Hne He Hc Hs Hcs Hok.
  - (* last iteration *)
    change (Z.of_nat 1) with 1%Z in *. change (Z.of_nat 0) with 0%Z. rewrite Z.mul_1_l in *. rewrite Z.mul_0_l, Z.add_0_r.
    assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
    destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia))) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers).
    exists regs'. destruct (Z.ltb_spec (i + 1) n); [lia|].
    cbn [pf_mem].
    split; [exact Hms|]. rewrite R10, R11, R12, R21, R19, R14, R15. subst n.
    repeat (split; [reflexivity|]). exact Rothers.
  - (* one iteration, then the rest *)
    rewrite Nat2Z.inj_succ in Hn, Hcs |- *. rewrite Nat2Z.inj_succ in Hcs |- *.
    assert (Hks : (0 <= Z.of_nat k * s)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
    destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia))) as (regs1 & Hms1 & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers).
    destruct (Z.ltb_spec (i + 1) n); [|lia].
    destruct (IH regs1 (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom
                 (i + 1)%Z e (c + s)%Z s n ltac:(rewrite Nat2Z.inj_succ; lia) R10 R11 R12 R21 R19 ltac:(lia) Hne He ltac:(lia) Hs
                 ltac:(rewrite Nat2Z.inj_succ; lia))
      as (regs2 & Hms2 & S10 & S11 & S12 & S21 & S19 & S14 & S15 & Sothers).
    { intros j Hj. eapply store_ok_mono; [apply wbytes_grows | apply Hok; lia]. }
    exists regs2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    rewrite S10, S11, S12, S21, S19, S14, S15.
    split; [reflexivity|]. split; [reflexivity|]. split; [f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|].
    split; [f_equal; f_equal; lia|]. split; [reflexivity|].
    intros r A B C D. rewrite (Sothers r A B C D). apply Rothers; assumption.
Qed.


(* [comment removed for export] *)
Lemma pf_wbytes_inside : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs))%Z ->
  wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
  cbn [wbytes length] in *.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Z.sub_diag. cbn [Z.to_nat nth].
    destruct rest as [|b' rest'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + cbn [length] in Hnw. rewrite wbytes_below.
      * rewrite bv_eqb_refl. reflexivity.
      * rewrite u_add1 by lia. cbn [length]. lia.
      * rewrite u_add1 by lia. lia.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
    rewrite Hu1.
    replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
      with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
    reflexivity.
Qed.

Lemma pf_wbytes_outside : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m a bs x = m x.
Proof.
  intros bs m a x Hnw [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
Lemma pf_mem_frame : forall k mem e c s i (a : word),
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  (bv_unsigned a < e - 4 * (i + Z.of_nat k) \/ e - 4 * i <= bv_unsigned a)%Z ->
  pf_mem mem e c s i k a = mem a.
Proof.
  induction k as [|k IH]; intros mem e c s i a Hi Hk He Ha; [reflexivity|].
  cbn [pf_mem]. rewrite IH by lia.
  apply pf_wbytes_outside; rewrite length_N_to_le_bytes, u64_of_Z by lia; cbn [Z.of_nat]; lia.
Qed.

Lemma word_to_le_bytes4_Z : forall v, word_to_le_bytes 4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof. intros v. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned. apply Z_to_le_bytes_wrap. cbn; lia. Qed.

(* [comment removed for export] *)
Lemma pf_mem_cell : forall k mem e c s i j t,
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= j < Z.of_nat k)%Z -> (t < 4)%nat ->
  pf_mem mem e c s i k (Z_to_bv 64 (e - 4 * (i + Z.of_nat k) + 4 * j + Z.of_nat t))
  = Some (nth t (Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16)) (Z_to_bv 8 0)).
Proof.
  induction k as [|k IH]; intros mem e c s i j t Hi Hk He Hj Ht; [lia|].
  rewrite Nat2Z.inj_succ in *.
  cbn [pf_mem].
  destruct (Z.eq_dec j (Z.of_nat k)) as [->|Hne].
  - (* the cell written by THIS iteration, untouched by the later ones *)
    rewrite pf_mem_frame; [| lia | lia | lia | rewrite u64_of_Z by lia; lia].
    rewrite pf_wbytes_inside; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; [| cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia].
    rewrite word_to_le_bytes4_Z. f_equal. f_equal; [lia|]. f_equal. f_equal. lia.
  - replace (e - 4 * (i + Z.succ (Z.of_nat k)) + 4 * j + Z.of_nat t)%Z
      with (e - 4 * ((i + 1) + Z.of_nat k) + 4 * j + Z.of_nat t)%Z by lia.
    rewrite (IH _ e (c + s)%Z s (i + 1)%Z j t) by lia.
    f_equal. f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma pf_mem_rdn : forall k mem e c s i j,
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= j < Z.of_nat k)%Z ->
  rdn segs (pf_mem mem e c s i k) (Z_to_bv 64 (e - 4 * (i + Z.of_nat k) + 4 * j)) 4
  = Some (Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16)).
Proof.
  intros k mem e c s i j Hi Hk He Hj.
  apply AX2S.rdn_pointwise; [apply length_Z_to_le_bytes | rewrite u64_of_Z by lia; cbn [Z.of_nat]; lia |].
  intros t Ht. rewrite u64_of_Z by lia. apply pf_mem_cell; assumption.
Qed.

Lemma pf_cell_linear : forall c s k j, (16 | s)%Z ->
  ((c + (k - 1 - j) * s) / 16 = (c + (k - 1) * s) / 16 + j * (- (s / 16)))%Z.
Proof.
  intros c s k j [q ->].
  replace (c + (k - 1 - j) * (q * 16))%Z with ((c + (k - 1) * (q * 16)) + (- (j * q)) * 16)%Z by lia.
  rewrite Z.div_add by lia. rewrite Z.div_mul by lia. lia.
Qed.

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
  intros regs mem rom i e c s n H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs Hwr.
  destruct (Z.to_nat (n - i)) as [|k] eqn:Hk; [lia|].
  assert (Hkz : (Z.of_nat (S k) = n - i)%Z) by lia.
  destruct (pf_loop k regs mem rom i e c s n ltac:(lia) H10 H11 H12 H21 H19 Hi Hne He Hc Hs ltac:(rewrite Hkz; exact Hcs))
    as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Ro).
  { intros j Hj. replace (e - 4 * (j + 1))%Z with (e - 4 * n + 4 * (n - j - 1))%Z by lia. apply Hwr; lia. }
  exists regs'. rewrite R10, R11, R12, R21, R19, R14, R15, Hkz.
  replace (Z.of_nat k) with (n - i - 1)%Z by lia.
  repeat (split; [first [exact Hms | reflexivity]|]). exact Ro.
Qed.


(* [comment removed for export] *)

Lemma pf_mem_wbytes : forall k mem e c s i,
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  pf_mem mem e c s i k = wbytes mem (Z_to_bv 64 (e - 4 * (i + Z.of_nat k))) (pf_bytes c s k).
Proof.
  intros k mem e c s i Hi Hk He. apply functional_extensionality. intros a.
  pose proof (u64_range a) as Ra. pose proof (pf_bytes_length c s k) as L.
  destruct (Z_lt_le_dec (bv_unsigned a) (e - 4 * (i + Z.of_nat k))) as [Hlt|Hge];
    [|destruct (Z_lt_le_dec (bv_unsigned a) (e - 4 * i)) as [Hlt2|Hge2]].
  - rewrite pf_mem_frame by lia. symmetry. apply pf_wbytes_outside; rewrite L, u64_of_Z by lia; lia.
  - set (base := (e - 4 * (i + Z.of_nat k))%Z) in *.
    set (j := ((bv_unsigned a - base) / 4)%Z). set (t := Z.to_nat ((bv_unsigned a - base) mod 4)).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (Hj : (0 <= j < Z.of_nat k)%Z) by (subst j base; lia).
    assert (Ht : (t < 4)%nat) by (subst t; lia).
    assert (Ha : a = Z_to_bv 64 (base + 4 * j + Z.of_nat t)).
    { apply bv_eq. rewrite u64_of_Z by (subst j t base; lia). subst j t base. lia. }
    rewrite Ha. subst base. rewrite (pf_mem_cell k mem e c s i j t Hi Hk He Hj Ht).
    rewrite pf_wbytes_inside; rewrite ?L, ?u64_of_Z by lia; [|lia|lia].
    replace (Z.to_nat (e - 4 * (i + Z.of_nat k) + 4 * j + Z.of_nat t - (e - 4 * (i + Z.of_nat k)))) with (Z.to_nat (4 * j) + t)%nat by lia.
    symmetry. f_equal. apply pf_bytes_nth; assumption.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - rewrite pf_mem_frame by lia. symmetry. apply pf_wbytes_outside; rewrite L, u64_of_Z by lia; lia.
Qed.

Theorem popfree_spec_of_code : popfree_spec segs p.
Proof.
  intros regs mem i e c s n H10 H11 H12 H21 H19 Hin He Hc Hs Hcs Hok.
  destruct (popfree_loop_run regs mem (seg_rom segs) i e c s n H10 H11 H12 H21 H19
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hc Hs Hcs) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Ro).
  { intros d m Hd Hdm. eapply (store_ok_sub segs mem _ _ (Z.to_nat (4 * (n - i))) m); [| exact Hok | |]; rewrite !u64_of_Z by lia; lia. }
  exists regs'. rewrite (pf_mem_wbytes (Z.to_nat (n - i)) mem e c s i) in Hms by lia.
  replace (i + Z.of_nat (Z.to_nat (n - i)))%Z with n in Hms by lia.
  split; [exact Hms|]. split; [exact R10|]. split; [exact R12|]. split; [exact R14|]. split; [exact R15|]. exact Ro.
Qed.

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
Variable rz : Z.

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
  | XPnScan => node_pnscan A nx0 rz cs
  | XLayout => node_layout rz cs args
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
  | [] => CErr 3 k (init_acs_of rz A)
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
Lemma stk_ok_init : forall segs inp mbase ph entry (sp brk0 : word)
    (rdraw : EntryDraw),
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
  stk_ok segs (wrap_mem inp mbase ph entry sp rdraw) sp stack_window_depth.
Proof.
  intros segs inp mbase ph entry sp brk0 rdraw Hvl Hlau a n H1 H2.
  unfold stack_window_depth in H1.
  apply (store_ok_wrap_window_valid segs inp mbase ph entry sp brk0 a n rdraw
           Hvl Hlau); lia.
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
Lemma wrap_mem_none_low :
  forall v inp mbase ph entry (sp brk0 : word) (rdraw : EntryDraw) (i : Z),
  entry_launch_ok_va v (mkEntry sp brk0 mbase rdraw) inp ->
  (0 <= i)%Z -> (i < bv_unsigned sp - stack_max_size)%Z ->
  wrap_mem inp mbase ph entry sp rdraw (Z_to_bv 64 i) = None.
Proof.
  intros v inp mbase ph entry sp brk0 rdraw i Hlau H0 Hi. unfold wrap_mem.
  pose proof (u64_range sp) as Hsp.
  pose proof (launch_sp_le_ed_top v inp mbase sp brk0 rdraw Hlau) as Htop.
  pose proof (Z.le_max_l (bv_unsigned (ed_top rdraw) - stack_max_size)
                (bv_unsigned mbase + stack_guard_gap_bytes (in_kernel inp))) as Hmax.
  assert (Hu : bv_unsigned (Z_to_bv 64 i) = i)
    by (apply u_small; unfold stack_max_size in Hi; lia).
  unfold stack_to_mem. rewrite Hu.
  replace (Z.leb (bv_unsigned sp) i) with false
    by (symmetry; apply Z.leb_gt; unfold stack_max_size in Hi; lia).
  replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) i) with false
    by (symmetry; apply Z.leb_gt; unfold stack_window_lo in *; lia).
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
