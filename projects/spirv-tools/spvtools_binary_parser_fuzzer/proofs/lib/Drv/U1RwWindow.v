(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec SeqExec StepTac StoreOk StreamSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1RwWindow () := "K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib9StreamSim7wseg_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrImgWTgt_spvtools_binary_parser_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega7EnvRing5PExpr01C49OSSVerify5KrLib7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC49OSSVerify5KrLib7StoreOk=store_ok_wsegC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C49OSSVerify5KrLib7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decK46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_ef000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_f0000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_f1000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_f2000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_f3000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_f4000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_f5000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_f6000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_f7000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_f8000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_f9000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_fa000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_fb000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_fc000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_fd000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_fe000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow;wsegw_ff000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow<wsegw_100000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow<wsegw_101000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow<wsegw_102000C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv:U1RwWindow<wsegw_103000C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02c59OSSVerify5KrLib3Drv:U1RwWindow9rw_wview_C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib3Drv:U1RwWindow;store_ok_rwC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma wsegw_ef000 : wseg_ok SEGS (Z_to_bv 64 0xef000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj15Tg000hj13Tg001Mj14Tg0022j19Tg002Pj28Tg0036j36Tg003lj37Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#5%32#3#4#3#3#3#3#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wsegw_f0000 : wseg_ok SEGS (Z_to_bv 64 0xf0000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2;Tg000Jj15Tg000hj14Tg0022j19Tg002Pj28Tg0036j36Tg003lj37Tg001Mj12Tg004Fj11Tf0R0#2#2p=:%20#2#2#2p=3%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1';g005eg007DR2#:#3#5%42#4#4#3#3#3#3#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wsegw_f1000 : wseg_ok SEGS (Z_to_bv 64 0xf1000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj15Tg000hj13Tg001Mj14Tg0022j19Tg002Pj28Tg0036j36Tg003lj37Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#5%32#3#3#4#2#3#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wsegw_f2000 : wseg_ok SEGS (Z_to_bv 64 0xf2000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj15Tg000hj13Tg001Mj14Tg0022j19Tg002Pj28Tg0036j36Tg003lj37Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#5%32#3#3#2#3#4#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wsegw_f3000 : wseg_ok SEGS (Z_to_bv 64 0xf3000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj17Tg000hj13Tg0022j19Tg002Pj28Tg0036j36Tg003lj35Tg001Mj14Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#7%32#3#3#2#3#3#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=501do"). Qed.
Lemma wsegw_f4000 : wseg_ok SEGS (Z_to_bv 64 0xf4000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2;Tg000Jj16Tg000hj14Tg001Mj12Tg0022j1:Tg002Pj29Tg0036j38Tg003lj37Tg004Fj11Tf0R0#2#2p=5%20#2#2#2p=3%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1';g005eg007DR2#5#3#6%42#4#4#2#4#5#3#3#3#:'9g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#038=701do"). Qed.
Lemma wsegw_f5000 : wseg_ok SEGS (Z_to_bv 64 0xf5000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj15Tg000hj13Tg001Mj14Tg0022j19Tg002Pj28Tg0036j36Tg003lj37Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#5%32#3#3#4#3#4#3#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wsegw_f6000 : wseg_ok SEGS (Z_to_bv 64 0xf6000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj15Tg000hj13Tg001Mj14Tg0022j19Tg002Pj28Tg0036j36Tg003lj37Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#5%32#3#3#4#3#3#4#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wsegw_f7000 : wseg_ok SEGS (Z_to_bv 64 0xf7000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj15Tg000hj13Tg001Mj14Tg0022j19Tg002Pj28Tg0036j36Tg003lj37Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#5%32#3#3#4#3#3#3#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wsegw_f8000 : wseg_ok SEGS (Z_to_bv 64 0xf8000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2;Tg000Jj16Tg000hj14Tg001Mj12Tg0022j1:Tg002Pj29Tg0036j38Tg003lj37Tg004Fj11Tf0R0#2#2p=5%20#2#2#2p=3%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1';g005eg007DR2#5#3#6%42#4#4#4#2#5#3#3#3#:'9g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#038=701do"). Qed.
Lemma wsegw_f9000 : wseg_ok SEGS (Z_to_bv 64 0xf9000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj17Tg000hj13Tg0022j19Tg002Pj28Tg0036j36Tg003lj35Tg001Mj14Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#7%32#3#3#3#2#3#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=501do"). Qed.
Lemma wsegw_fa000 : wseg_ok SEGS (Z_to_bv 64 0xfa000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj15Tg000hj13Tg001Mj14Tg0022j19Tg002Pj28Tg0036j36Tg003lj37Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#5%32#3#3#3#4#3#4#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wsegw_fb000 : wseg_ok SEGS (Z_to_bv 64 0xfb000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj15Tg000hj13Tg001Mj14Tg0022j19Tg002Pj28Tg0036j36Tg003lj37Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#5%32#3#3#3#4#3#3#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wsegw_fc000 : wseg_ok SEGS (Z_to_bv 64 0xfc000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2;Tg000Jj16Tg000hj13Tg0022j1:Tg002Pj29Tg0036j38Tg003lj37Tg001Mj12Tg004Fj11Tf0R0#2#2p=5%20#2#2#2p=4%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1';g005eg007DR2#5#4#6%32#3#3#3#3#5#4#4#4#:'9g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#038=701do"). Qed.
Lemma wsegw_fd000 : wseg_ok SEGS (Z_to_bv 64 0xfd000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj15Tg000hj13Tg001Mj14Tg0022j19Tg002Pj28Tg0036j36Tg003lj37Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#5%32#3#3#3#3#4#3#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wsegw_fe000 : wseg_ok SEGS (Z_to_bv 64 0xfe000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj15Tg000hj13Tg001Mj14Tg0022j19Tg002Pj28Tg0036j36Tg003lj37Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#5%32#3#3#3#3#3#4#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wsegw_ff000 : wseg_ok SEGS (Z_to_bv 64 0xff000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj17Tg000hj13Tg0022j19Tg002Pj28Tg0036j36Tg003lj35Tg001Mj14Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007DR2#2#2#2#7%32#3#3#3#3#3#3#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=501do"). Qed.
Lemma wsegw_100000 : wseg_ok SEGS (Z_to_bv 64 0x100000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj15Tg0022j19Tg002Pj28Tg0036j37Tg003lj36Tg001Mj12Tg004Fj11Tf0R0#2#2p=4%20#2#2#2p=3%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007D#4#3R2#5%42#3#3#3#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#037=601do"). Qed.
Lemma wsegw_101000 : wseg_ok SEGS (Z_to_bv 64 0x101000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj14Tg001Mj13Tg000hj19Tg0022j18Tg002Pj27Tg0036j35Tg003lj36Tg004Fj11Tf0R0#3#3p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007D#2#2#2R2#4%32#9#2#2#2#2#2#2#8'7g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#035=601do"). Qed.
Lemma wsegw_102000 : wseg_ok SEGS (Z_to_bv 64 0x102000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj15Tg000hj14Tg001Mj13Tg0022j19Tg002Pj28Tg0036j36Tg003lj37Tg004Fj11Tf0R0#3#3p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007D#2#2#2R2#5%42#3#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=701do"). Qed.
Lemma wsegw_103000 : wseg_ok SEGS (Z_to_bv 64 0x103000) 0x1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1RwWindow ()) [] "p;2p;1p;3g0000j2:Tg000Jj17Tg000hj13Tg0022j19Tg002Pj28Tg0036j36Tg003lj35Tg001Mj14Tg004Fj11Tf0R0#4#4p=2%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g004eR0g005ER1':g005eg007D#2#2#2R2#7%32#3#2#2#2#2#2#2#9'8g007i#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#036=501do"). Qed.

Lemma wsegw_104000 : wseg_ok SEGS (Z_to_bv 64 0x104000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_105000 : wseg_ok SEGS (Z_to_bv 64 0x105000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_106000 : wseg_ok SEGS (Z_to_bv 64 0x106000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_107000 : wseg_ok SEGS (Z_to_bv 64 0x107000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_108000 : wseg_ok SEGS (Z_to_bv 64 0x108000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_109000 : wseg_ok SEGS (Z_to_bv 64 0x109000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_10a000 : wseg_ok SEGS (Z_to_bv 64 0x10a000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_10b000 : wseg_ok SEGS (Z_to_bv 64 0x10b000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_10c000 : wseg_ok SEGS (Z_to_bv 64 0x10c000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_10d000 : wseg_ok SEGS (Z_to_bv 64 0x10d000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_10e000 : wseg_ok SEGS (Z_to_bv 64 0x10e000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_10f000 : wseg_ok SEGS (Z_to_bv 64 0x10f000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_110000 : wseg_ok SEGS (Z_to_bv 64 0x110000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_111000 : wseg_ok SEGS (Z_to_bv 64 0x111000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_112000 : wseg_ok SEGS (Z_to_bv 64 0x112000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_113000 : wseg_ok SEGS (Z_to_bv 64 0x113000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_114000 : wseg_ok SEGS (Z_to_bv 64 0x114000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_115000 : wseg_ok SEGS (Z_to_bv 64 0x115000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_116000 : wseg_ok SEGS (Z_to_bv 64 0x116000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_117000 : wseg_ok SEGS (Z_to_bv 64 0x117000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_118000 : wseg_ok SEGS (Z_to_bv 64 0x118000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_119000 : wseg_ok SEGS (Z_to_bv 64 0x119000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_11a000 : wseg_ok SEGS (Z_to_bv 64 0x11a000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_11b000 : wseg_ok SEGS (Z_to_bv 64 0x11b000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_11c000 : wseg_ok SEGS (Z_to_bv 64 0x11c000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_11d000 : wseg_ok SEGS (Z_to_bv 64 0x11d000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_11e000 : wseg_ok SEGS (Z_to_bv 64 0x11e000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_11f000 : wseg_ok SEGS (Z_to_bv 64 0x11f000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_120000 : wseg_ok SEGS (Z_to_bv 64 0x120000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_121000 : wseg_ok SEGS (Z_to_bv 64 0x121000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_122000 : wseg_ok SEGS (Z_to_bv 64 0x122000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wsegw_123000 : wseg_ok SEGS (Z_to_bv 64 0x123000) 0x1000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rw_wview_ : forall m (x : word), (0xef000 <= bv_unsigned x < 0x124000)%Z -> wview SEGS m x <> None.
Proof.
  intros m x Hx.
  assert (C : forall lo : Z, wseg_ok SEGS (Z_to_bv 64 lo) 4096 = true -> (0 <= lo)%Z -> (lo + 4096 <= 2 ^ 64)%Z ->
              (lo <= bv_unsigned x < lo + 4096)%Z -> wview SEGS m x <> None).
  { intros lo W H0 H1 Hr.
    apply (store_ok_all SEGS m 4096 (Z_to_bv 64 lo)); [rewrite u_Z2bv by lia; lia | | rewrite u_Z2bv by lia; lia].
    apply store_ok_wseg; exact W. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf0000%Z).
  { apply (C 0xef000%Z wsegw_ef000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf1000%Z).
  { apply (C 0xf0000%Z wsegw_f0000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf2000%Z).
  { apply (C 0xf1000%Z wsegw_f1000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf3000%Z).
  { apply (C 0xf2000%Z wsegw_f2000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf4000%Z).
  { apply (C 0xf3000%Z wsegw_f3000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf5000%Z).
  { apply (C 0xf4000%Z wsegw_f4000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf6000%Z).
  { apply (C 0xf5000%Z wsegw_f5000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf7000%Z).
  { apply (C 0xf6000%Z wsegw_f6000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf8000%Z).
  { apply (C 0xf7000%Z wsegw_f7000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xf9000%Z).
  { apply (C 0xf8000%Z wsegw_f8000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xfa000%Z).
  { apply (C 0xf9000%Z wsegw_f9000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xfb000%Z).
  { apply (C 0xfa000%Z wsegw_fa000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xfc000%Z).
  { apply (C 0xfb000%Z wsegw_fb000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xfd000%Z).
  { apply (C 0xfc000%Z wsegw_fc000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xfe000%Z).
  { apply (C 0xfd000%Z wsegw_fd000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0xff000%Z).
  { apply (C 0xfe000%Z wsegw_fe000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x100000%Z).
  { apply (C 0xff000%Z wsegw_ff000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x101000%Z).
  { apply (C 0x100000%Z wsegw_100000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x102000%Z).
  { apply (C 0x101000%Z wsegw_101000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x103000%Z).
  { apply (C 0x102000%Z wsegw_102000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x104000%Z).
  { apply (C 0x103000%Z wsegw_103000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x105000%Z).
  { apply (C 0x104000%Z wsegw_104000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x106000%Z).
  { apply (C 0x105000%Z wsegw_105000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x107000%Z).
  { apply (C 0x106000%Z wsegw_106000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x108000%Z).
  { apply (C 0x107000%Z wsegw_107000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x109000%Z).
  { apply (C 0x108000%Z wsegw_108000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x10a000%Z).
  { apply (C 0x109000%Z wsegw_109000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x10b000%Z).
  { apply (C 0x10a000%Z wsegw_10a000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x10c000%Z).
  { apply (C 0x10b000%Z wsegw_10b000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x10d000%Z).
  { apply (C 0x10c000%Z wsegw_10c000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x10e000%Z).
  { apply (C 0x10d000%Z wsegw_10d000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x10f000%Z).
  { apply (C 0x10e000%Z wsegw_10e000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x110000%Z).
  { apply (C 0x10f000%Z wsegw_10f000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x111000%Z).
  { apply (C 0x110000%Z wsegw_110000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x112000%Z).
  { apply (C 0x111000%Z wsegw_111000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x113000%Z).
  { apply (C 0x112000%Z wsegw_112000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x114000%Z).
  { apply (C 0x113000%Z wsegw_113000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x115000%Z).
  { apply (C 0x114000%Z wsegw_114000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x116000%Z).
  { apply (C 0x115000%Z wsegw_115000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x117000%Z).
  { apply (C 0x116000%Z wsegw_116000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x118000%Z).
  { apply (C 0x117000%Z wsegw_117000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x119000%Z).
  { apply (C 0x118000%Z wsegw_118000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x11a000%Z).
  { apply (C 0x119000%Z wsegw_119000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x11b000%Z).
  { apply (C 0x11a000%Z wsegw_11a000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x11c000%Z).
  { apply (C 0x11b000%Z wsegw_11b000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x11d000%Z).
  { apply (C 0x11c000%Z wsegw_11c000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x11e000%Z).
  { apply (C 0x11d000%Z wsegw_11d000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x11f000%Z).
  { apply (C 0x11e000%Z wsegw_11e000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x120000%Z).
  { apply (C 0x11f000%Z wsegw_11f000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x121000%Z).
  { apply (C 0x120000%Z wsegw_120000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x122000%Z).
  { apply (C 0x121000%Z wsegw_121000); lia. }
  destruct (Z_lt_le_dec (bv_unsigned x) 0x123000%Z).
  { apply (C 0x122000%Z wsegw_122000); lia. }
  apply (C 0x123000%Z wsegw_123000); lia.
Qed.

Lemma store_ok_rw : forall m (a : word) n,
  (0xef000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x124000)%Z -> store_ok SEGS m a n = true.
Proof.
  intros m a n Hlo Hhi.
  apply (store_ok_of_all SEGS n m a); [lia | intros x Hx; apply rw_wview_; lia].
Qed.

Lemma store_ok_rwZ : forall m (a : Z) n,
  (0xef000 <= a)%Z -> (a + Z.of_nat n <= 0x124000)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros m a n Hlo Hhi.
  apply store_ok_rw; rewrite u_Z2bv by lia; lia.
Qed.
