(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (16 recorded proofs replaced by written proofs (pf_bytes_length, pf_bytes_nth, pf_bytes_cell and 13 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AxSymExec3Sound.
From Stdlib Require Import FunctionalExtensionality.
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From Stdlib Require Import Zify.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanPopFree () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr09K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib2AS;AsanPopFree3PW0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5instr08c59OSSVerify5KrLib2AS;AsanPopFree3PW1C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop06c59OSSVerify5KrLib2AS;AsanPopFree3PW2C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c59OSSVerify5KrLib2AS;AsanPopFree3PW3C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5instr0:c59OSSVerify5KrLib2AS;AsanPopFree3PW4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07c59OSSVerify5KrLib2AS;AsanPopFree3PW5C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib2AS;AsanPopFree3PW6C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05c59OSSVerify5KrLib2AS;AsanPopFree3PW7C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib2AS;AsanPopFree8pf_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib2AS7CatExecDlength_Z_to_le_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:length_appC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega6VarMap1t01K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z4succC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02C35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List8app_nth1C47Corelib4Init3Nat3subK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC46Stdlib5Lists4List8app_nth2K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z3maxI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_geI47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op204C47Corelib5Lists7ListDef6firstnI47Corelib4Init5Peano2le00C46Stdlib5Lists4List;firstn_all2C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List8firstn_0C56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List:firstn_appC47Corelib5Lists7ListDef5skipnC46Stdlib5Lists4List7skipn_0C46Stdlib5Lists4List:skipn_all2C46Stdlib5Lists4List9skipn_appC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC45stdpp9bitvector;definitions4BvWfC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib2AS8PropExec6v_srliC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z4lxorC69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S;lxor_ones64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SymExec:v_addi_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib2AS8PropExec6v_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_rC59OSSVerify5KrLib2AS8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib2AS8PropExec9step_srliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9step_xoriC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9step_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9step_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8step_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SymExec;step_sw_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4btgtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5c_ltuC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib2AS8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec<step_bltu_tkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SymExec8btgt_litC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec<step_bltu_ftC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree8u64_of_ZC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula0:c59OSSVerify5KrLib2AS;AsanPopFree>asanreflect_fxC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto4kind02K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib2AS;AsanPopFree3PD0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree3PD1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree3PD2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree3PD3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree3PD4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree3PD5C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree3PD6C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree3PD7C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00c59OSSVerify5KrLib2AS;AsanPopFree6pf_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_1_lc59OSSVerify5KrLib2AS;AsanPopFree7pf_iterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7mul_0_lC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC59OSSVerify5KrLib2AS7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim<msteps_transC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib2AS8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6u_add1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8sub_diagC47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib2AS7CatExec<wbytes_aboveC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib2AS7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFreeApf_wbytes_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExecBZ_to_le_bytes_wrapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFreeCword_to_le_bytes4_ZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree@pf_wbytes_insideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree<pf_mem_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree;pf_mem_cellC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S=rdn_pointwiseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z7div_addc59OSSVerify5KrLib2AS;AsanPopFree7pf_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree?pf_bytes_lengthC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC47Corelib4Init5Logic6eq_symC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extc59OSSVerify5KrLib2AS;AsanPopFree<pf_bytes_nthC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC59OSSVerify5KrLib2AS8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree@popfree_loop_runC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree=pf_mem_wbytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanPopFree<popfree_specC1?~~~~~~~~~~~~~~~".
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

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
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) [] "p;2p;1p;3p;4p;6p10000p4p710p1000Mp4p710R0p8p1000kp4p710P0p8p1001Fp4p710P0p8g001ej2BTg002Ej1ATg002gj19Tg003Xj10Tg004=j12Tg004bj15Tg005@j13Tg005^j31Tg006Aj48Tg006mj47Tg007Mj26Tg007oj34j1:Tg008Ij4@Tg008gj2?Tg009Dj6<Tg009\j2;Tg00:6j2=Tg00:Tj3>Tg00;<R0g00;hR1'BR2#AR3g00<F#9R4P0P1g00==g00=iR5#0R6#2#5R7%25R5#2#0#3g00>NR831%05R5#0#3=178%55%06#3R6;18C8P6C7,62R634R8P3P3%:3P0g00>jP1g00?[C@,?2P4P6E<R6g00@4R4g00@TR2';1=86=442d3>o"). Qed.
Lemma PD1 : decode_any PW1 = Some (OpImm ALU_XOR 15 10 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) [] "p;2p;1p;3p;4p;6g001ej2CTg002Ej1BTg002gj1:Tg003Xj11Tg004=j12Tg004bj16Tg005@j13Tg005^j34Tg00A4j49Tg006mj47Tg007Mj28Tg007oj35j1ATg008Ij4@Tg008gj2?Tg009Dj6<Tg009\j2=Tg00:6j2>Tg00:Tj3;Tf0#2#2p=0g00;<R0g00;hR1'CR2#BR3g00A`#:R4P0P1g00BWg00=iR5#1R6#2R7#6R8%25R5#0R9#3g00>NR:34%17#3=48:%15#1#6%09#0#0#0#3;4:C9%16#3C7,82R635R:P3P3%A3P0g00>jP1g00?[C@,?2P4P6E<R6g00@4R4g00@TR2'=1>:6=542d3;o"). Qed.
Lemma PD2 : decode_any PW2 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) [] "p;2p;1p;3p;4p;6g001ej2BTg002Ej1ATg002gj19Tg003Xj10Tg004=j15Tg004bj13Tg005@j11Tg005^j32Tg00A4j48Tg006mj47Tg007Mj26Tg007oj34j1:Tg008Ij4@Tg008gj2?Tg009Dj6<Tg009\j2;Tg00:6j2=Tg00:Tj3>Tg00;<R0g00;hR1'BR2#AR3g00CC#9R4P0P1g00D:g00=iR5#0R6#5R7#3%07#1g00>NR732R8P8%55#0#0#3%15;27C8%06#1C7,62R634R7P3P3%:3P0g00>jP1g00?[C@,?2P4P6E<R6g00@4R4g00@TR2';1=76=442d3>o"). Qed.
Lemma PD3 : decode_any PW3 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) [] "p;2p;1p;3p;4p;6g001ej2BTg002Ej1ATg002gj19Tg003Xj11Tg004=j10Tg004bj15Tg005@j12Tg005^j33Tg006Aj48Tg006mj47Tg007Mj26Tg007oj34j1:Tg008Ij4@Tg008gj2?Tg009Dj6<Tg009\j2;Tg00:6j2=Tg00:Tj3>Tg00;<R0g00;hR1'BR2#AR3g00Df#9R4P0P1g00E]g00=iR5#1R6#0#5%05R5#0#0#2g00>NR733R8P8%15#5%26;37C8%16#2C7,62R634R7P3P3%:3P0g00>jP1g00?[C@,?2P4P6E<R6g00@4R4g00@TR2';1=76=442d3>o"). Qed.
Lemma PD4 : decode_any PW4 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) [] "p;2p;1p;3p;4p;6g001ej2BTg002Ej1ATg002gj18Tg003Xj13Tg004=j10Tg004bj1:Tg005@j11Tg005^j32Tg00FIj47Tg006mj46Tg007Mj25Tg007oj34j19Tg008Ij4@Tg008gj2?Tg009Dj6;Tg009\j2<Tg00:6j2=Tg00:Tj3>Tg00;<R0g00;hR1'BR2#AR3g00G5#8R4P0P1g00D:g00=iR5#3R6#0R7#:R8%05#0#0#1g00>NR532R9%07#1=285P9C7%36#1C6,52R634R9P3P3%93P0g00>jP1g00?[C@,?2P4P6E;R6g00@4R4g00@TR2'<1=96=442d3>o"). Qed.
Lemma PD5 : decode_any PW5 = Some (Store SZ4 15 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) [] "p;2p;1p;3p;4p;6g001ej2BTg002Ej1ATg002gj19Tg003Xj10Tg004=j11Tg004bj15Tg005@j13Tg005^j32Tg00Glj48Tg006mj47Tg007Mj26Tg007oj34j1:Tg008Ij4@Tg008gj2?Tg009Dj6<Tg009\j2;Tg00:6j2=Tg00:Tj3>Tg00;<R0g00;hR1'BR2#AR3g00HX#9R4P0P1g00IOg00=iR5#0R6#1#5R7%15R5#1R8#1#3g00>NR932%08#3=279%05#0#5g00J;;29C8%06#3C7,62R634R9P3P3%:3P0g00>jP1g00?[C@,?2P4P6E<R6g00@4R4g00@TR2';1=96=442d3>o"). Qed.
Lemma PD6 : decode_any PW6 = Some (Op ALU_ADD 12 12 21, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) [] "p;2p;1p;3p;4p;6g001ej2BTg002Ej1ATg002gj18Tg003Xj10Tg004=j12Tg004bj1:Tg005@j11Tg005^j33Tg00FIj47Tg006mj46Tg007Mj25Tg007oj34j19Tg008Ij4@Tg008gj2?Tg009Dj6;Tg009\j2<Tg00:6j2=Tg00:Tj3>Tg00;<R0g00;hR1'BR2#AR3g00JY#8R4P0P1g00D:g00=iR5#0R6#2R7#:R8%25#0#0#1g00>NR533R9P9%07#2#1=385C7%06#1C6,52R634R5P3P3%93P0g00>jP1g00?[C@,?2P4P6E;R6g00@4R4g00@TR2'<1=56=442d3>o"). Qed.
Lemma PD7 : decode_any PW7 = Some (Branch BC_LTU 10 19 8164, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFree ()) [] "p;2p;1p;3p;4p;6g001ej2BTg002Ej1ATg002gj19Tg003Xj11Tg004=j10Tg004bj15Tg005@j12Tg005^j33Tg00KPj48Tg006mj47Tg007Mj26Tg007oj34j1:Tg008Ij4@Tg008gj2?Tg009Dj6<Tg009\j2;Tg00:6j2=Tg00:Tj3>Tg00;<R0g00;hR1'BR2#AR3g00L<#9R4P0P1g00M3g00=iR5#1R6#0R7#5R8%17#2g00>NR733%16R6#0#0#2=387%05R5#1#0#5%05#0#0#0#0#0#1#1#0#1#1#2;37C8%26C7,62R634R7P3P3%:3P0g00>jP1g00?[C@,?2P4P6E<R6g00@4R4g00@TR2';1=76=442d3>o"). Qed.

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
  (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
    change (Z.of_nat 1) with 1%Z in *. change (Z.of_nat 0) with 0%Z. rewrite Z.mul_1_l in *. rewrite Z.mul_0_l, Z.add_0_r.
    assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
    destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia))) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers).
    exists regs'. destruct (Z.ltb_spec (i + 1) n); [lia|].
    cbn [pf_mem].
    split; [exact Hms|]. rewrite R10, R11, R12, R21, R19, R14, R15. subst n.
    repeat (split; [reflexivity|]). exact Rothers.
  - (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
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
