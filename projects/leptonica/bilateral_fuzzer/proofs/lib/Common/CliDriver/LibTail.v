(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk AgentLib SymExec RefMemcpyLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_LibTail () := "C47Corelib7Program6Basics4flipI45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC59OSSVerify5KrLib6Common8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3addc69OSSVerify5KrLib6Common9CliDriver7LibTail7zbv_modC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_modC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC46Stdlib6ZArith4Zdiv:Zminus_modC59OSSVerify5KrLib6Common8PropExec5v_subC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7mul_modC59OSSVerify5KrLib6Common8PropExec5v_mulC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc69OSSVerify5KrLib6Common9CliDriver7LibTail6word_ZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_ZZC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc69OSSVerify5KrLib6Common9CliDriver7LibTail7vsub_ZZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver7LibTail7vmul_ZZC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01C59OSSVerify5KrLib6Common8PropExec7alu_subC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02C59OSSVerify5KrLib6Common8PropExec5m_mulC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01C59OSSVerify5KrLib6Common8PropExec7alu_xorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_xorC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop06C59OSSVerify5KrLib6Common8PropExec8alu_sltuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_sltuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01C35stdpp7tactics<f_equal_helpK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3ltbC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC45stdpp9bitvector;definitions9bv_signedK46Stdlib9micromega5Tauto8GFormula0:C59OSSVerify5KrLib6Common8AgentLib?bv_signed_smallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK46Stdlib9micromega5Tauto4kind02I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9w_add_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SeqExec7rdn_appC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K45stdpp9bitvector;definitions2bv01C46Stdlib5Lists4List2InC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC45stdpp9bitvector;definitions4BvWfC47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic4True01I47Corelib4Init5Logic2or00C59OSSVerify5KrLib6Common<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Peano2ltC69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib6Common9CliDriver8SymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3addC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z:mod_uniqueK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib6Common8PropExec7v_addiwC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32c69OSSVerify5KrLib6Common9CliDriver7LibTail@v_addiw_id_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7w_addiwC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver:SymDriveH4?low32_zero_sextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SeqExec7rdn_nthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib5Lists4List8app_nth1C46Stdlib5Lists4List6nth_In".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma zbv_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP1"] "h01zh12Hah22b1h32b2h41nh51Hh67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__witp;1p;3p;2p;4p;7p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9g000Nj14Tg0011j32Tg001Kj20Tg0025j3RTg002Yj11Tg003>j1MTg003\j1=Tg004:j2BTg004Wj25Tg0057j28Tg005]j27Tg006Cj2?Tg006kj2>Tg007Gj29Tg007cj3QTg008Gj1PTg008gj1OTg009Gj1NTg009ej1LTg00:Cj1KTg00:nj2<Tg00;Qj3DTg00<4j4CTg00<_j7ETg00=Cj6FTg00=gj2GTg00>Ij2HTg00>cj2ATg00?Oj3ITg00?nj4JTg00@`j3@Tg00AAj1;Tg00BCj66Tg00Baj2:Tg00CPR1f1R0f0R232p=3g00CnR3%42R4%40R5g00DLf2R6#4?202f3R7/061070'3R8[10601062'3%47?260[R9f4#4?276\8AR602P2n2001000000120000000W3W2W4P9^35^24^43P2g00Dg#1R3#1#1#1#1#1R4#MR5%=3R3%=4R4'BR9,50R8,85R71850R:P11758R;1856,05,32X01P11750R<1569R=,75/32X01P115891756,32X01P1P815=9/32X011?34g00ELR=/>319=41>=9[[19=3R>g00EjR?AQ340UW119=9\?^1>g00FFR>#P%O>%N1%L1%K1R>g00G2R?g00GQR4P4g00H1R@P>P?P4P4P@P11<13=D15g00HQ1<1=CCg00I8FEEF1G>@P2P6g00IXR@g00J8R>'H1A26=2@>dAI1=0CJb7b:b;A219=g00JX[P2b6b8b99@09P<%;0E6P;%;8E6105:1:50E610571:58E6O4b5X01o"). Qed.
End VP1.

Section VP2. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vadd_ZZ : forall x y, v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP2"] "h01zh12Hah27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__with81bh91xh:1yp;1p;2p;3p;4p;7p;6g002Yj13Tg003>j1TTg005]j26Tg000Nj1CTg0057j20Tg001Kj2>Tg00K5j22Tg0011j31Tg003\j1<Tg004:j2DTg004Wj24Tg00KRj18Tg006Cj2@Tg006kj2?Tg007Gj27Tg007cj3STg008Gj1RTg008gj1QTg009Gj1PTg009ej1OTg00:Cj1NTg00:nj2;Tg00;Qj3MTg00<4j4LTg00<_j7KTg00=Cj6ETg00=gj2FTg00>Ij2GTg00>cj2HTg00?Oj3ITg00?nj4JTg00LWj4BTg00M8j69Tg00AAj1=Tg00BCj65Tg00Baj2:Tg00MTj2ATg00CPR0P0g00Dg#3R1#3#3#3#3#3R2#TR3f1R4'6R5%C3R6f0R71034R8,>3R9'2,03f2R:/24,03R;31X00P01637R<163:/27,03=16;X00P0%<1R1%<2R2'DR=,44R>1275,03=16;X00P0147=R?14:=/27,03=16;X00P612>?R?/4=R>,03A167;X86P01247R@/4=1037RA=16;X00%8@P>P4P7P=1@12g00ELR>/?117>21?>=[[17>1R;g00EjRBAS124UW117>=\B^1;g00FFR;#R%Q;%P0%O0%N0R;g00G2RBg00GQR2P2g00H1RCP;PBP2P2PCP01;01=M03g00HQ1;0>CLg00I8FKEE1F;CP7P:g00IXRCg00J8R;'G1H7:=1C;dAI0>4CJb3b6b7A10=>g00JX[P7b2b4b5CBE9103?%8?E9P<%=7E5P5%=4E51>3A1:37E5P91:34E51A8A103@516eX:0W9o"). Qed.
End VP2.

Section VP3. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vsub_ZZ : forall x y, v_sub (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP3"] "h01zh11bh21xh31yp;1p;2p;3p;6g002Yj13Tg003>j1ATg005]j26Tg000Nj1>Tg0057j20Tg001Kj29Tg00NNj22Tg0011j31Tg003\j18Tg004:j2?Tg004Wj24Tg00KRj17Tg00Nkj3=Tg00M8j6<Tg00AAj1;Tg00BCj65Tg00Baj2:Tg00OKj2@Tg00CPR0P0g00Dg#3R1#3#3#3#3#3R2#AR3f1R4'6R5%>3R6f0R71034R8,93R9'2,03f2R:/24,03R;31X00P01637R<163:/27,03=16;X00P0%81%82'?R2,44R11275,03=16;X00P01472R=14:2/27,03=16;X00P6121=R=/42R1,03A167;X16P01247R:/421037R>=16;X00%7:P1A=472E<103=%7=E<P<%;7E5P5%;4E5193>1:37E5P91:34E51@8>103:516eX30W2o"). Qed.
End VP3.

Section VP4. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vmul_ZZ : forall x y, v_mul (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x * y).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP4"] "h01zh12Hah27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__with81bh91xh:1yp;1p;2p;3p;4p;7p;6g002Yj13Tg003>j1TTg005]j26Tg000Nj1CTg0057j20Tg001Kj2>Tg00PEj22Tg0011j31Tg003\j1<Tg004:j2DTg004Wj24Tg00KRj18Tg006Cj2@Tg006kj2?Tg007Gj27Tg007cj3STg008Gj1RTg008gj1QTg009Gj1PTg009ej1OTg00:Cj1NTg00:nj2;Tg00;Qj3MTg00<4j4LTg00<_j7KTg00=Cj6ETg00=gj2FTg00>Ij2GTg00>cj2HTg00?Oj3ITg00?nj4JTg00Pbj4BTg00M8j69Tg00AAj1=Tg00BCj65Tg00Baj2:Tg00QCj2ATg00CPR0P0g00Dg#3R1#3#3#3#3#3R2#TR3f1R4'6R5%C3R6f0R71034R8,>3R9'2,03f2R:/24,03R;31X00P01637R<163:/27,03=16;X00P0%<1R1%<2R2'DR=,44R>1275,03=16;X00P0147=R?14:=/27,03=16;X00P612>?R?/4=R>,03A167;X86P01247R@/4=1037RA=16;X00%8@P>P4P7P=1@12g00ELR>/?117>21?>=[[17>1R;g00EjRBAS124UW117>=\B^1;g00FFR;#R%Q;%P0%O0%N0R;g00G2RBg00GQR2P2g00H1RCP;PBP2P2PCP01;01=M03g00HQ1;0>CLg00I8FKEE1F;CP7P:g00IXRCg00J8R;'G1H7:=1C;dAI0>4CJb3b6b7A10=>g00JX[P7b2b4b5CBE9103?%8?E9P<%=7E5P5%=4E51>3A1:37E5P91:34E51A8A103@516eX:0W9o"). Qed.
End VP4.

Section VP5. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma word_Z : forall w : word, w = Z_to_bv 64 (bv_unsigned w).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP5"] "h01wp;1p;2p;4g002Yj10Tg003>j16Tg000Nj12Tg001Kj21Tg0057j25Tg00R=j24Tg00Roj43Tg00Dg#0#0#0#0#0#0#6R0#2R1P1f0R1,10,50P11401C3W0o"). Qed.
End VP5.

(* [comment removed for export] *)
Section VP6. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vadd_wZ : forall (w : word) y, v_add w (Z_to_bv 64 y) = Z_to_bv 64 (bv_unsigned w + y).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP6"] "h01yh15lemmah21wh31xp;1p;2p;3p;4p;:p;9g002Yj10Tg003>j1BTg000Nj19Tg001Kj23Tg0057j21Tg0011j3<j1;Tg00SKj18Tg00MTR0j22Tg00T;j44Tg00Tbj17Tg00UQj45Tg00VHj3:Tg00W>j26Tg00Wjl:ATg00K5j2@Tg00XWl9=Tg00YQj1>Tg00ZUj2?Tg00Dg#0#0#0#0#0#0#BR1#9R2g00CPf1R31313R4,115<2P2%;2R5%82f2R61113R7'21316R8,11R9/27P2^02R:^32R;P2P:P5P2P2P5P5C4R<C4R=P2P:P<P2P2P5%72C5C59:;=P0P6P9f0R9P7P71627M:A1@83,11R1P11621M9=W1%>31?49O2W0W2o"). Qed.
End VP6.
Section VP7. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vadd_Zw : forall x (w : word), v_add (Z_to_bv 64 x) w = Z_to_bv 64 (x + bv_unsigned w).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP7"] "h05lemmah11wh21xh31yp;1p;2p;3p;4p;;p;9g002Yj10Tg003>j1CTg000Nj19Tg001Kj23Tg0057j21Tg0011j3<j1;Tg00SKj18Tg00MTR0j22Tg00T;j44Tg00Tbj17Tg00UQj45Tg00VHj3:Tg00Wjj4BTg00W>j26Tg00[Zl;ATg00K5j2=Tg00XWl9>Tg00YQj1?Tg00ZUj2@Tg00CPg00Dg#0#0#0#0#0#0#CR1#9R2f0R31313R4,115<2P2%;2R5%82f2R6,11R7f1R8'21318R9,11R:,27P2P2^32R;P5P2P2P5P5C4R<P0P;\2R=P2P;P5P<C4R>P2P;P<P2P2P5%72C5C59:=>P0CBP71627P8P:P3M;A1=69,11R1P11621M9>W0%?31@84O2W1W2o"). Qed.
End VP7.
Section VP8. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vadd_ww : forall (w w' : word), v_add w w' = Z_to_bv 64 (bv_unsigned w + bv_unsigned w').
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP8"] "h01wh12w'p;1p;2g002Yj10Tg003>j16Tg000Nj12Tg001Kj21Tg00K5j25Tg0057j24Tg00>Ij23Tg00Dg#0#0#0#0#0#0#6R0#2R1f1,10f0,10'5,40,31X11W0o"). Qed.
End VP8.
Section VP9. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vsub_wZ : forall (w : word) y, v_sub w (Z_to_bv 64 y) = Z_to_bv 64 (bv_unsigned w - y).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP9"] "h01yh15lemmah21wh31xp;1p;2p;3p;4p;:p;9g002Yj10Tg003>j1BTg000Nj19Tg001Kj23Tg0057j21Tg0011j3<j1;Tg00SKj18Tg00OKR0j22Tg00T;j44Tg00Tbj17Tg00UQj45Tg00VHj3:Tg00W>j26Tg00Wjl:ATg00NNj2@Tg00XWl9=Tg00YQj1>Tg00\Uj2?Tg00Dg#0#0#0#0#0#0#BR1#9R2g00CPf1R31313R4,115<2P2%;2R5%82f2R61113R7'21316R8,11R9/27P2^02R:^32R;P2P:P5P2P2P5P5C4R<C4R=P2P:P<P2P2P5%72C5C59:;=P0P6P9f0R9P7P71627M:A1@83,11R1P11621M9=W1%>31?49O2W0W2o"). Qed.
End VP9.
Section VP10. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vsub_Zw : forall x (w : word), v_sub (Z_to_bv 64 x) w = Z_to_bv 64 (x - bv_unsigned w).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP10"] "h05lemmah11wh21xh31yp;1p;2p;3p;4p;;p;9g002Yj10Tg003>j1CTg000Nj19Tg001Kj23Tg0057j21Tg0011j3<j1;Tg00SKj18Tg00OKR0j22Tg00T;j44Tg00Tbj17Tg00UQj45Tg00VHj3:Tg00Wjj4BTg00W>j26Tg00[Zl;ATg00NNj2=Tg00XWl9>Tg00YQj1?Tg00\Uj2@Tg00CPg00Dg#0#0#0#0#0#0#CR1#9R2f0R31313R4,115<2P2%;2R5%82f2R6,11R7f1R8'21318R9,11R:,27P2P2^32R;P5P2P2P5P5C4R<P0P;\2R=P2P;P5P<C4R>P2P;P<P2P2P5%72C5C59:=>P0CBP71627P8P:P3M;A1=69,11R1P11621M9>W0%?31@84O2W1W2o"). Qed.
End VP10.
Section VP11. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vmul_wZ : forall (w : word) y, v_mul w (Z_to_bv 64 y) = Z_to_bv 64 (bv_unsigned w * y).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP11"] "h01yh15lemmah21wh31xp;1p;2p;3p;4p;:p;9g002Yj10Tg003>j1BTg000Nj19Tg001Kj23Tg0057j21Tg0011j3<j1;Tg00SKj18Tg00QCR0j22Tg00T;j44Tg00Tbj17Tg00UQj45Tg00VHj3:Tg00W>j26Tg00Wjl:ATg00PEj2@Tg00XWl9=Tg00YQj1>Tg00]Zj2?Tg00Dg#0#0#0#0#0#0#BR1#9R2g00CPf1R31313R4,115<2P2%;2R5%82f2R61113R7'21316R8,11R9/27P2^02R:^32R;P2P:P5P2P2P5P5C4R<C4R=P2P:P<P2P2P5%72C5C59:;=P0P6P9f0R9P7P71627M:A1@83,11R1P11621M9=W1%>31?49O2W0W2o"). Qed.
End VP11.
Section VP12. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vmul_Zw : forall x (w : word), v_mul (Z_to_bv 64 x) w = Z_to_bv 64 (x * bv_unsigned w).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP12"] "h05lemmah11wh21xh31yp;1p;2p;3p;4p;;p;9g002Yj10Tg003>j1CTg000Nj19Tg001Kj23Tg0057j21Tg0011j3<j1;Tg00SKj18Tg00QCR0j22Tg00T;j44Tg00Tbj17Tg00UQj45Tg00VHj3:Tg00Wjj4BTg00W>j26Tg00[Zl;ATg00PEj2=Tg00XWl9>Tg00YQj1?Tg00]Zj2@Tg00CPg00Dg#0#0#0#0#0#0#CR1#9R2f0R31313R4,115<2P2%;2R5%82f2R6,11R7f1R8'21318R9,11R:,27P2P2^32R;P5P2P2P5P5C4R<P0P;\2R=P2P;P5P<C4R>P2P;P<P2P2P5%72C5C59:=>P0CBP71627P8P:P3M;A1=69,11R1P11621M9>W0%?31@84O2W1W2o"). Qed.
End VP12.

(* [comment removed for export] *)
Section VP13. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma ed_add : forall E a b, edenot E (EAlu ALU_ADD a b) = v_add (edenot E a) (edenot E b).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP13"] "h01Eh11ah21bp;2p;1p;3g00^_j21Tg00_hj27Tg002Yj10Tg003>j12Tg000Nj16Tg00`dj35Tg00MTj24Tg0011j33Tg00amg00c5R0f2R1f1R2'1R3f0R4,11R5'7g00Dg#0#0#0#0#0#0#2#6g00d>?524,11143533eX20W1W0o"). Qed.
End VP13.
Section VP14. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma ed_sub : forall E a b, edenot E (EAlu ALU_SUB a b) = v_sub (edenot E a) (edenot E b).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP14"] "h01Eh11ah21bp;2p;1p;3g00^_j21Tg00djj27Tg002Yj10Tg003>j12Tg000Nj16Tg00`dj35Tg00OKj24Tg0011j33Tg00amg00c5R0f2R1f1R2'1R3f0R4,11R5'7g00Dg#0#0#0#0#0#0#2#6g00ef?524,11143533eX20W1W0o"). Qed.
End VP14.
Section VP15. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma ed_mul : forall E a b, edenot E (EMd M_MUL a b) = v_mul (edenot E a) (edenot E b).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP15"] "h01Eh11ah21bp;2p;1p;3g00^_j21Tg00fRj27Tg002Yj10Tg003>j12Tg000Nj16Tg00gLj35Tg00QCj24Tg0011j33Tg00amg00c5R0f2R1f1R2'1R3f0R4,11R5'7g00Dg#0#0#0#0#0#0#2#6g00hU?524,11143533eX20W1W0o"). Qed.
End VP15.
Section VP16. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma ed_xor : forall E a b, edenot E (EAlu ALU_XOR a b) = v_xor (edenot E a) (edenot E b).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP16"] "h01Eh11ah21bp;2p;1p;3g00^_j21Tg00iAj27Tg002Yj10Tg003>j12Tg000Nj16Tg00`dj35Tg00j=j24Tg0011j33Tg00amg00c5R0f2R1f1R2'1R3f0R4,11R5'7g00Dg#0#0#0#0#0#0#2#6g00k7?524,11143533eX20W1W0o"). Qed.
End VP16.
Section VP17. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma ed_sltu : forall E a b, edenot E (EAlu ALU_SLTU a b) = v_sltu (edenot E a) (edenot E b).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP17"] "h01Eh11ah21bp;2p;1p;3g00^_j21Tg00kcj27Tg002Yj10Tg003>j12Tg000Nj16Tg00`dj35Tg00l`j24Tg0011j33Tg00amg00c5R0f2R1f1R2'1R3f0R4,11R5'7g00Dg#0#0#0#0#0#0#2#6g00m[?524,11143533eX20W1W0o"). Qed.
End VP17.
Section VP18. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma ed_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP18"] "h01Eh11zp;1p;2g002Yj10Tg003>j14Tg000Nj12Tg0057j21Tg00>Ij23Tg00amg00CPg00Dg#0#0#0#0#0#0#4R0#2f0,10'3W1W0o"). Qed.
End VP18.
Section VP19. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma ed_var : forall E n, edenot E (EVar n) = ev E n.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP19"] "h01Eh11np;1p;2g002Yj10Tg003>j14Tg000Nj12Tg00nGj21Tg00>Ij23Tg00amg00oLg00Dg#0#0#0#0#0#0#4#2f1f0'1'3W1W0o"). Qed.
End VP19.

(* [comment removed for export] *)
Ltac not_arith t :=
  lazymatch t with
  | v_add _ _ => fail | v_sub _ _ => fail | v_mul _ _ => fail | Z_to_bv _ _ => fail
  | _ => idtac
  end.

Ltac ed_lin pins :=
  rewrite ?ed_add, ?ed_sub, ?ed_mul, ?ed_lit, ?ed_var, ?alu_add, ?alu_sub, ?m_mul; cbn [ev];
  pins;
  repeat match goal with
         | |- context [v_add (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vadd_ZZ x y)
         | |- context [v_sub (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vsub_ZZ x y)
         | |- context [v_mul (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vmul_ZZ x y)
         | |- context [v_add ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vadd_wZ w y)
         | |- context [v_add (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vadd_Zw x w)
         | |- context [v_sub ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vsub_wZ w y)
         | |- context [v_sub (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vsub_Zw x w)
         | |- context [v_mul ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vmul_wZ w y)
         | |- context [v_mul (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vmul_Zw x w)
         | |- context [v_add ?w ?w'] => not_arith w; not_arith w'; rewrite (vadd_ww w w')
         end.

Ltac ed_lin_in H pins :=
  rewrite ?ed_add, ?ed_sub, ?ed_mul, ?ed_lit, ?ed_var, ?alu_add, ?alu_sub, ?m_mul in H; cbn [ev] in H;
  pins;
  repeat match type of H with
         | context [v_add (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vadd_ZZ x y) in H
         | context [v_sub (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vsub_ZZ x y) in H
         | context [v_mul (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vmul_ZZ x y) in H
         | context [v_add ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vadd_wZ w y) in H
         | context [v_add (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vadd_Zw x w) in H
         | context [v_sub ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vsub_wZ w y) in H
         | context [v_sub (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vsub_Zw x w) in H
         | context [v_mul ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vmul_wZ w y) in H
         | context [v_mul (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vmul_Zw x w) in H
         | context [v_add ?w ?w'] => not_arith w; not_arith w'; rewrite (vadd_ww w w') in H
         end.

(* [comment removed for export] *)
Section VP20. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma adenot_off_shift : forall E b k d k',
  (k' = k + d)%Z ->
  (0 <= bv_unsigned (edenot E b) + k)%Z -> (bv_unsigned (edenot E b) + k < 2 ^ 64)%Z ->
  Z_to_bv 64 (bv_unsigned (adenot E (SA b k)) + d) = adenot E (SA b k').
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP20"] "h04__x1h14__x2h22Hah37__arithh44__ffh56__sat2h66__sat3h78__varmaph85__with94__x3h:2k'h;1Eh<1Hh=2H0h>2H1h?1bh@1dhA1khB1zp;2p;3p;1p;4p;8p;7p;6g00K5j20Tg0011j35Tg002Yj17Tg003>j1KTg00^_j24Tg001Kj2;Tg003\j1@Tg004:j2QTg006kj26Tg000Nj1ITg00okj2:Tg0115j29Tg0057j22j1^Tg00>Ij2DTg006Cj2ZTg007cj3YTg008Gj1XTg008gj1WTg012>j2BTg012\j4ATg009ej1VTg00:Cj1UTg013:j2<Tg013]j38Tg014@j1RTg00<4j4=Tg00=gj2PTg00>cj2JTg00?Oj3LTg00?nj4MTg014ej8NTg009Gj1OTg00:nj2?Tg00;Qj3HTg015Bj1STg015dj7TTg00DLj2`Tg016Hj2_Tg00BCj6ETg017Xj1CTg018aj1FTg007Gj2]Tg00<_j7\Tg019ij8[Tf2R0f1R1';f0R2'0p=1g00ELR3/]2p=3P1g00G2R4g00GQR5P5g00H1R6P2g00I8F\p=>f3R7P4P5P5P6P0P1P2G[p=Gg00amg00c5g00CPR810019582P81070g00DgR9#7R:#7#7#7#7#7R;#KR<f6R=f5R>'4f4R?31R@#3f7RA/4=,;<RB/0>RC%@:RD%@;R;'QRE'6%I<RFf8RG1:A='9=1<>,2<1:A0,9G35[[X:814>?=1<7#316@EP8PC102>,2<14GA10=>51<,2<55FXB8P8PF%^<R@P@10C?10>?RH,0BPF\8/D@1ZD;R@163D%3;163E[[RB%3DRIg00EjRJAYD;1UW2R;%3E\J^2IRIg00FFRJ#XRK%WJRJP81B80RLP11B87CA%V8RM%U8RNP81<89RO1<8:R:588RP%R9,<8R9588g00HQA88:9988OC='>1PN6ROP2P0g00IXR9g00J8R:'D1J20=59:dAL831CMR:b4b7b8X08X18X981021R9/001010RQ,02558^08^18^98P2PAPGf:f9'4,;<RRO3b3b5b6GN12<C,;<P@PBP;PIPKPJP8PLP1%O8CAPMPNP8PPg01:M1?8D=H8<C=,>NRD%S5RMPNP81?83g01;4PPC=,>NRPPMPNP4P5P5P6PPPDFTCGCGPOP:b4b7b8X08X18169E%3Q1007R0#3160E'`[[^08^18P2PGPRP7P?O4b3b5b6,_CEE1:=>R>#C,4A%F>51<,2<=1<?,2<1:=HRH#C,4A%FH51<,2<55Fe19A>=1<?,2<19AH55FeW>W=P1P2EEW<X:8X@8WAW?W;o"). Qed.
End VP20.

(* [comment removed for export] *)
Section VP21. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma eqb_ZZ : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP21"] "h02Hah17__arithh26__sat1h36__sat2h44__x1h51zh64__ffh78__varmaph85__with91ah:1bp;2p;1p;3p;4p;7p;8p;6g007Gj21Tg002Yj10Tg003\j1=Tg004:j2BTg006kj24Tg00DLj2<Tg003>j1LTg0057j29Tg001Kj25Tg01;[j22Tg0011j33Tg00>Ij2>Tg006Cj2?Tg007cj3RTg008Gj1QTg008gj1PTg012>j2OTg009ej1NTg00:Cj1MTg00:nj2;Tg013:j2KTg00<4j46Tg00;Qj3FTg015dj7ETg015Bj1DTg019ij8GTg00=gj2HTg00>cj2CTg00?Oj3ITg00?nj4JTg016Hj27Tg00BCj68Tg01<8j3ATg00<_j7@Tf1R0g00G2R1g00GQR2P2g00H1R3f0R4g00I8F@p=:g00CPR5g00ELR6/10g00DgR7#0R8#=R9%08#0#0#0#0R8#=R:'BR;,40'<R<P5f3R=g00IXR>%L8R8198=R?'5R@,24f4RA/2=RB33X55P5f2RC12A4=3>BX5512=CRB,>>198CRD,581?9:RE1469116:146;[[RF1169RGg00EjRHAR9:0UW0R:116;\H^0GRGg00FFRH#Q%PH1O50%N5%M5RHP1P2P2P3PHP1P2P2P3P51;56g01;41K57R7C6,:HP5P7g01:M1;59=F58C6,:HFER9%D2P9GG1HH3P4PCg00J8RH,>>1C4C=3>HdAI560CJb6b7b8X45R01164144;'<P<[^45R;P4f5P=O2b1b2b3,7CE8P@PEPFP:PGP0P;P4f6PAO2b1b2b3,7=E8AA8?D=3>BeV<UX:5W9o"). Qed.
End VP21.
Section VP22. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma ltu_ZZ : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.ltb a b.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP22"] "h02Hah17__arithh26__sat1h36__sat2h44__x1h51zh64__ffh78__varmaph85__with91ah:1bp;2p;1p;3p;4p;7p;8p;6g007Gj21Tg002Yj10Tg003\j1=Tg004:j2BTg006kj24Tg00DLj2<Tg003>j1LTg0057j29Tg001Kj25Tg01<ej22Tg0011j33Tg00>Ij2>Tg006Cj2?Tg007cj3RTg008Gj1QTg008gj1PTg012>j2OTg009ej1NTg00:Cj1MTg00:nj2;Tg013:j2KTg00<4j46Tg00;Qj3FTg015dj7ETg015Bj1DTg019ij8GTg00=gj2HTg00>cj2CTg00?Oj3ITg00?nj4JTg016Hj27Tg00BCj68Tg01=Bj3ATg00<_j7@Tf1R0g00G2R1g00GQR2P2g00H1R3f0R4g00I8F@p=:g00CPR5g00ELR6/10g00DgR7#0R8#=R9%08#0#0#0#0R8#=R:'BR;,40'<R<P5f3R=g00IXR>%L8R8198=R?'5R@,24f4RA/2=RB33X55P5f2RC12A4=3>BX5512=CRB,>>198CRD,581?9:RE1469116:146;[[RF1169RGg00EjRHAR9:0UW0R:116;\H^0GRGg00FFRH#Q%PH1O50%N5%M5RHP1P2P2P3PHP1P2P2P3P51;56g01;41K57R7C6,:HP5P7g01:M1;59=F58C6,:HFER9%D2P9GG1HH3P4PCg00J8RH,>>1C4C=3>HdAI560CJb6b7b8X45R01164144;'<P<[^45R;P4f5P=O2b1b2b3,7CE8P@PEPFP:PGP0P;P4f6PAO2b1b2b3,7=E8AA8?D=3>BeV<UX:5W9o"). Qed.
End VP22.
Section VP23. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma lts_ZZ : forall a b, (0 <= a < 2 ^ 63)%Z -> (0 <= b < 2 ^ 63)%Z ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.ltb a b.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP23"] "h04__x1h12Hah27__arithh36__sat0h46__sat1h54__ffh68__varmaph75__with84__x2h91zh:2Hbh;1ah<1bp;2p;1p;3p;4p;7p;6p;8g007Gj24Tg002Yj10Tg003\j1<Tg014@j12Tg004:j2VTg006kj25Tg00DLj2=Tg003>j17Tg0057j2:Tg01=oj28Tg01<ej21Tg0011j33Tg006Cj2CTg007cj3UTg008Gj1TTg008gj1STg012>j2>Tg009Gj1QTg012\j4PTg009ej1NTg00:Cj1MTg013:j29Tg00<4j46Tg00<_j7;Tg01>Wj6LTg00=gj2KTg00>Ij2JTg00>cj2HTg00?Oj3GTg00?nj4ITg00:nj2@Tg00;Qj3FTg015dj7ETg015Bj1DTg019ij8OTg01?;j2ATg00BCj6BTg01@?j3RTf1R0g00G2R1g00GQR2P2g00H1R3f0R4g00I8R5F;p=?g00CPR6g00ELR7/40g00DgR8#0R9#<R:%28#2#2#2#2R;#<R<'VR=,50'=R>P6f3R?g00IXR@%09#0#0#0#0#7RA1:A?RB'8RC,14f4RD/1?RE33X96P6f2RF11D4=3@EX961C:<RE157:147<157=[[RG147:RHg00EjRIAU:<0UW1R<147=\I^1HRHg00FFRI#TRJ%SIRIP61>6FP0%Q6CP%N6RK%M6RLP1P2P2PLP1P2P2g01@lP61968R8g01:MRM1969C6P5F;R5P5EL1KL3R5P4PFg00J8R9,J@1H4F=3@9dAG670CIR9b5b6b7X06X861140RN=3@N^06^86P4f5RNf6ROO2b2b3b41:AFRP,8APEPGP<PHPJPI1>60PKPLP1P2P2P3PLP1P2P2P3P61@67g01;4P8C6,?LP6P8PM1@6:%7;5F6C6,?LFERL%D2PLGOP5P9b5b6b7X06R91474154='=P>[^06R=P4PNP?O2b2b3b4,AFEBPCPEPGP<PHP9P=P4POPDO2b2b3b4,A?EBARABP11?F53@eX:>W1X<6W;o"). Qed.
End VP23.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (u_small z) by lia
      end
  end.

(* [comment removed for export] *)
Section VP24. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma rdn_app_Z : forall segs m a n1 n2 b1 b2,
  rdn segs m (Z_to_bv 64 a) n1 = Some b1 ->
  rdn segs m (Z_to_bv 64 (a + Z.of_nat n1)) n2 = Some b2 ->
  (0 <= a)%Z -> (a + Z.of_nat n1 < 2 ^ 64)%Z ->
  rdn segs m (Z_to_bv 64 a) (n1 + n2) = Some (b1 ++ b2).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP24"] "h02Hah14__x1h24__x2h32H1h42H2h52Hnh67__arithh74__ffh86__sat3h96__sat4h:8__varmaph;5__with<1ah=1bh>2b1h?2b2h@4cstrhA1mhB2n1hC2n2hD4segshE1zp;1p;2p;4p;3p;7p;6p;9p;8g008gj1=Tg002Yj11Tg003>j1@Tg000Nj1DTg01ALj1FTg0057j23Tg01Anj48Tg01Bfj2ATg0011j34Tg01CHj12Tg00K5j25Tg003\j1CTg004:j2eTg006kj26Tg001Kj2XTg01Chj1WTg006Cj2UTg007cj3TTg01DMj1:Tg01Dlj2<Tg01EUj3BTg01F>j2QTg008Gj1PTg01Fjj3OTg012>j2NTg009Gj1MTg012\j4LTg009ej1KTg00:Cj1JTg00:nj2?Tg013:j2>Tg00<4j47Tg015Bj1ITg013]j3HTg00;Qj3RTg015dj7GTg00=gj2STg00>Ij2dTg00>cj2cTg00?Oj3bTg00?nj4]Tg00DLj2\Tg016Hj2YTg00BCj6ETg01GJj1ZTg01HEj3[Tg01Hjj2VTg01J<l9^Tg007Gj2_Tg00<_j7`Tg019ij8aTg00ELR0f0R1'_p=0f1R2g00G2R3g00GQR4P4g00H1R5P1g00I8F`p=9f3R6P3P4P4P5f2R7P2P1Gap=;g01K7#=g00DgR8#1R9#1#1R:#1#1#1R;#@R<#DR=%@:#DR:#F[g00CPR>g00oLR?%=:R:%F:R@f6RAf5RBf4RC,3<P6C81A:2RD34f7REPA%2C,5B,3<P6C8=4@D%0A%2A,5E%C9RD%C;R;'eRF'6f:RGf9PEPAf8RA,3<RHPBPCP6P=1X<HRI%2ERJ'5,3<f;RKPGP1PEC81A:BRL54@X==P>PAPKPG%2A,51,3<PEC8=4@LXE>P7PI%WE%0J1UD;160D%0;160F[[%0DRJg00EjRIATD;2UW0%0F\I^0Jg00FFRJg01L6RI#:#:R;#:,<>1<>;1<>I5B>5B>g01LU'Q%PJ3O%=JP>1N>7P2%M>CL%K>%J>RJP>1?>0RIg01;4R;1>>9R9C7,9J%I4RLPJP>1>>8R8=H>9g01:MR91?>D=R><RDC7,9JPLPJP>PIP;P8C7,9JR;PLPJP3P4P4P5P;P>P8P9PDC7,9JFGC;C;C;1SJ5P1P7g00IXRJg00J8R5'd1c17=4J5dAb>02C]b7b:b;X1>X2>%021527/6F%07%06166F'\[[[^1>^2>P1%2Kf<P6PCPBO5b6b8b9b@,YAEE%ZE9[<H1VHEEEM9^W5W0W4W3X?:W>XC?WBW<WAWDo"). Qed.
End VP24.

Section VP25. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma callee_saved_no0 : ~ In (0%bv : reg) callee_saved.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP25"] "p'0h03Hinh11Hh21ei001zp;1p;3p;2p;6g002Yj18Tg014@j19Tg003>j1>Tg000Nj1=Tg01MAj3:Tg008Gj1?Tg01Fjj34Tg01Mdj30Tg0011j31Tg001Kj1<j22Tg01N;j2DTg01NZj1;Tg01O3j2CTg003\j1BTg01OVj6@Tg00M8j6ATf1R0f0R1#Bg01P3R23:p=6f4g00CPR3f3R4f2R5P0P1E@p=7A1301p=5P3P4P5P2P0P1EAp=3g00DgR0#8R5#9R4#>R6#=R7g00ELR8=:62R91660R:1665R;%90R0,66R<%85R5,66R=%85,66R>%95R5,66R?%85,66R@%95,66R5%84RA#8,66RB%9A,66RA%94R4#8,66RC%94,66R4%80R0#8RD#8,66RE%9D,66RD%90R0#8,66RF%90,66R0%?7RG547RH547RI547RJ547RK547RL547RM547RN547RO547RP547RQ547RR547RS547RT547RU547RV54730RWg01PORXA17:9RYA079VRVg00JXRZP1P7%<6R[P:P9P1D7126:R:1269R\'5P:P3p-0P1PZg00EjPZn011000003001000010000X23R3P\P1C3PZ1DZ1R:b1b0X0YP1O1PXA17;9RYA079URUPZP1P7P[P;P9P1D7126;R;/5\P;P3P\P1C3PZP:b1b0X0YP1O1PXA17<9RYA079TRTPZP1P7P[P<P9P1D7126<R</5\P<P3P\P1C3PZP:b1b0X0YP1O1PXA17=9RYA079SRSPZP1P7P[P=P9P1D7126=R=/5\P=P3P\P1C3PZP:b1b0X0YP1O1PXA17>9RYA079RRRPZP1P7P[P>P9P1D7126>R>/5\P>P3P\P1C3PZP:b1b0X0YP1O1PXA17?9RYA079QRQPZP1P7P[P?P9P1D7126?R?/5\P?P3P\P1C3PZP:b1b0X0YP1O1PXA17@9RYA079PRPPZP1P7P[P@P9P1D7126@R@/5\P@P3P\P1C3PZP:b1b0X0YP1O1PXA1759RYA079OROPZP1P7P[P5P9P1D71265R5/5\P5P3P\P1C3PZP:b1b0X0YP1O1PXA17B9RYA079NRNPZP1P7P[PBP9P1D7126BRB/5\PBP3P\P1C3PZP:b1b0X0YP1O1PXA17A9RYA079MRMPZP1P7P[PAP9P1D7126ARA/5\PAP3P\P1C3PZP:b1b0X0YP1O1PXA17C9RYA079LRLPZP1P7P[PCP9P1D7126CRC/5\PCP3P\P1C3PZP:b1b0X0YP1O1PXA1749RYA079KRKPZP1P7P[P4P9P1D71264R4/5\P4P3P\P1C3PZP:b1b0X0YP1O1PXA17E9RYA079JRJPZP1P7P[PEP9P1D7126ERE/5\PEP3P\P1C3PZP:b1b0X0YP1O1PXA17D9RYA079IRIPZP1P7P[PDP9P1D7126DRD/5\PDP3P\P1C3PZP:b1b0X0YP1O1PXA17F9RYA079HRHPZP1P7P[PFP9P1D7126FRF/5\PFP3P\P1C3PZP:b1b0X0YP1O1PXA1709RXA079GRGPZP1P7P[P0P9P1D71260R0/5\P0P3P\P1C3PZP:b1b0X0XP1O1P1X0GP1O1n200100000021000010000X0HP1O1n200100000021000011000X0IP1O1n200100000021000011000X0JP1O1n200100000021000011000X0KP1O1n200100000021000011000X0LP1O1n200100000021000011000X0MP1O1n200100000021000011000X0NP1O1n200100000021000011000X0OP1O1n200100000021000011000X0PP1O1n201100000021000011000X0QP1O1n201100000021000011000X0RP1O1n201100000021000011000X0SP1O1n201100000021000011000X0TP1O1n201100000021000011000X0UP1O1n201100000021000011000X0VP1O1n201100000021000011000W0%;WeP21C68d9:68P7eg01Pi507#;eo"). Qed.
End VP25.

(* [comment removed for export] *)
Section VP26. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vals_ev_junk : forall vals R i, (i < 32)%nat ->
  vals_ev (vals ++ junk_vals R) (length vals + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP26"] "h01ih12Hih21Rh31bh44valsp;1p;2p;3p;4p;6g002Yj11Tg003>j18Tg000Nj1=Tg008gj1:Tg014@j1HTg01Qnj2ETg01RZj2<Tg01S2j1;Tg01T:j26Tg01CHj14Tg0057j23Tg01U>j25Tg0011j39Tg00>Ij2GTg01V7j2FTg01VSj4DTg01Voj4@Tg01WKj6?Tg00BCj67Tg01XUj3>Tg01Y2j2ATg01YRj2BTg01Yij3CTg01DMj12Tf0R0#2#2#2#2p=0g00Dg#1R1#1#1#1#1#1#8R2#=R3#:%H1#8R1/E3g00oLR4g01L6R5#0#0#0#0#0#0#0#0R6,<0P3f2R7#;R8f1R9'6R:f3R;%47,31'59930X33R<P3%49,31,57R7P<1G37P3P9P4P3%40,31,5;X04R41F56CDg00EL,32R2C@P3P4P9P6P2P0E?E7A93:7eA>3;81A3;/B9'6AC;89E7W1W0W2W4o"). Qed.
End VP26.

(* [comment removed for export] *)
Section VP27. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma v_addiw_id_errno : forall x : word,
  (2 ^ 64 - 4095 <= bv_unsigned x)%Z -> v_addiw x 0 = x.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP27"] "h04__x1h11Hh22Hah32H0h47__arithh54__ffh64__p1h76__sat0h86__sat1h98__varmaph:5__with;6__sat2h<6__sat3h=1zh>6__sat4h?6__sat5h@2b1hA2b2hB1nhC2HrhD2HxhE1xp;1p;2p;3p;4p;6p;7p;8g002Yj1:Tg003>j1KTg000Nj1;Tg003\j1=Tg004:j2LTg014@j1HTg00NNj23Tg001Kj20Tg007Gj29Tg01[6j1UTg006kj21Tg00DLR0j26Tg01\4j2RTg0057j2QTg0011j38Tg0025j3_Tg005]j2^Tg004Wj2<Tg00K5j24Tg006Cj2GTg007cj3FTg01POj2ATg008Gj1[Tg008gj1ZTg012>j2YTg009ej1XTg00:Cj1WTg013:j2VTg00:nj2BTg00;Qj3ETg00<4j4>Tg015Bj1TTg01\[j3DTg013]j3JTg01]>j6nTg00=gj2mTg00>Ij2lTg00>cj2kTg00?Oj3iTg00?nj4hTg00PEj2NTg01]bj3PTg01^Ej6OTg01^ij1aTg00Roj4`Tg00M8j6bTg00AAj1cTg00BCj6ITg00Baj2dTg01_Gj1eTg01_hj2]Tg00<_j7fTg015dj7gTg01`dj7\Tg019ij8jTf0R1#H#Hp=?g00ELR2/91p=2g00CPR3f1R4;81p=5P4g00G2R5g00GQR6P6g00H1R7P1g00I8Ffp=7P3P4g01;4P1C>p=Cf2R8P5P6P6P7P4P1Fgp=MP8P5P6P6P7P4P1F\p=Sf3R9P5P6P6P7P8P4P1Gjp=@g00DgR:#:R;#:#:#:#:R<#:R=#KR>#;R?%=;R;%==R='LR@%?:#?RA#H#?#?#?#=RB'3RC10>1'9%U410>4RD#211D@'6P310>8RD%K<RE/R1,Q>=8?9X=3g00CnRF%;1RG%;4RHP0%;8?84110981094'5RI[10841081'5%;9?884[RJf4RK#;?898\IA_841P1n2001000000120000000WAW@WBPJ^AH^@G^BFP1P>10>9RF,RERG,Q>RHP9P31^>GRJ10>KRI,51X=3RLP31<G@RMPL%=ARL,L;RN,4FRO%=<R<,L;RPPP13O@RQ1G;<RR112;RS%2<112P[[RT%2;RUg00EjRVAF;<4UW2R<%2P\V^2URW1G;LRX%2L112N[\SRYAF;L4VVX2URL%2N\V^2URZ1G;=R[%2=112@[\SRSAF;=4VVX2UR=%2@\V^2URUP0f9,0>RV#2R\11V@R]f:R^,0>R_/4NR`/3@Ra#211aP'611Pa19a2'6'Af7Rbf;,0>Rc#2Rdf<,0>/1@Rep-0Rfg00FFRg#[Rh%ZgRg1Y34Ri%X3Rj%W3RkP31V3:Rlg01:MRm1B3;R;=E3>RnC>,7kRo%T6RpPk1B3B9D3n/Cl,7kRBPp1B32Rq%KA9E3;RA9J3lRr=D3nRs'C,7kP3PsPmAE3;ER;C>,7k5MkPkP5P6P6P7P9EnR65SkC@C@1mk7R7P1P8g00IXR5g00J8RE'l1k18=85EdAi324ChREb5b9b:X03W6111@R519C4RC148N/3@Rm#211mP'6/A9[[^03^6fP1f>,0>Rm/4N/3@Rt,1P19t2'6PmP4f=RtO4b4W3W1P4P1O2n2001000010121000000b7b8b;b<b>b?PRPTP<PWPXPYPLPZP[PSP=PUP0P\P]1NPPR\/4a,5`PbPhPgPiPjP3Prg00HQRrAP3;;=J3sC>,7kP7PEb5b9b:X03141NR;13;@R;,4\'5^03P1PmO1b4X3eX1dP4P1O2n2001000000121000000b7b8b;b<b>b?EO1<OP,5QP314INRQ/3@RO131N/<@f5,0>'5X=3P3PI13ONRO/<@POP@%a:R:PIP[PSP=PUP0f6RI,0>RO#211O@10>bRb#211b@'611@b19b2'6'APKf8,0>RK#2RbPhPgPiPjPkPoPpPkPBPp1Cql,7k=Mko=Sk6C@C@P7PEb5b9b:X03X6f%28118@'6/A9\C\5^03^6fP111@c19c2'6PcP4P^O4b4X3]W1P4P1O2n2001000000121000000b7b8PXPYPLPZP[PSP=PUP0Pb11K@14VN/3@/3N1N@:RK/4V'5PI%2_11c@PhPgPiPjP3AD3sAPr1B3:9P3n=J3lC>,7kP7PEb5b9b:X0313;N14K1'5^03P110>tO1b4W3W1P4P1O2n2001000000121000000b7b8b;b<EOC`1<QPP1Ebb115MFePJ%cGEI10>H1d>GEIO4b114D2%eDEI1]82=8?8ebCWDWEo"). Qed.
End VP27.

Section VP28. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma edenot_addw0_errno : forall E a,
  (2 ^ 64 - 4095 <= bv_unsigned (edenot E a))%Z ->
  edenot E (EAluw ALU_ADD a (ELit 0)) = edenot E a.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP28"] "h01bh11Eh22Hah31ap;1p;2p;3p;6g002Yj10Tg003\j13Tg004:j2@Tg014@j17Tg00NNj2GTg003>j14Tg00^_j22Tg001Kj2>Tg007Gj2=Tg000Nj19Tg01MAj3<Tg01aHj35Tg01b3j18Tg01b[j3;Tg0011j36Tg01=oj2FTg01_hj2ETg01cCj2DTg01dQj2ATg00BCj6:Tg0057j2BTg01eMj1?Tg01fVj3CTf0R0#7#7p=1g00amg00c5g00DgR1#0R2#3%02#0#0#0R2#0R3#3'@%71R1#1#1#1#1#1#3'G%43R3f1R4/20'>'=%42R2#9R5%01#0#4R1g00ELR6g01P35<1R7752R8%93R9g00d>R:f3f2R;'2R<#8;;09523;6<X05P912;4R51F17'EA690<X091D50%85=;:895231A57E:1B36#8g01g_E:%?69C:4,2;=695eW2W3W1o"). Qed.
End VP28.

(* [comment removed for export] *)
Section VP29. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma rdn_byte_Z : forall segs m a n bs j,
  rdn segs m (Z_to_bv 64 a) n = Some bs -> (j < n)%nat -> (0 <= a)%Z -> (a + Z.of_nat j < 2 ^ 64)%Z ->
  rdn segs m (Z_to_bv 64 (a + Z.of_nat j)) 1%nat = Some [nth j bs (Z_to_bv 8 0)].
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP29"] "h02Hah11Rh24__x1h34__x2h41Hh52Hjh63Hj0h72Hnh87__arithh94__ffh:6__sat1h;6__sat2h<8__varmaph=5__with>1ah?1bh@2bshA4cstrhB5cstr0hC1jhD1mhE1nhF4segshG1zp;1p;2p;4p;3p;8p;6p;7p;<g008gj1>Tg002Yj14Tg003>j1GTg000Nj1CTg01ALj1LTg0057j21Tg01Anj45Tg01Bfj29Tg0011j33Tg01RZR0j2DTg01CHR1j12Tg00K5j27Tg003\j1OTg004:j2jTg006kR2j26Tg01hoj8aTg01GJj1MTg01HEj3KTg01DMj1?Tg01Voj4:Tg008Gj1HTg01Fjj38Tg001Kj2FTg01Hjj2ZTg00M8j6ETg00>Ij2=Tg01ijj4XTg01Chj1JTg006Cj2WTg007cj3VTg01Dlj2ATg01EUj3BTg01F>j2UTg012>j2TTg009Gj1QTg012\j4PTg009ej1RTg00:Cj1STg00:nj2NTg013:j2ITg00<4j4<Tg015Bj1iTg013]j3hTg00;Qj3gTg015dj7fTg00=gj2`Tg00>cj2_Tg00?Oj3^Tg00?nj4]Tg00DLj2bTg016Hj2cTg007Gj2\Tg01jQl<dTg00<_j7eTg019ij8[Tg00ELR3f0R4'\p=0g00oLR5g00CPR6P0P1P2g01k6f5R2f4R1f3R0f2R7f1R8P4M<dp=YP8g00G2R9g00GQR:P:g00H1R;P4g00I8Fep=;P0P9P:P:P;P7P8P4G[p=@g01K7#>g00DgR<#4R=#4#4R>#4#4#4R?#GR@#CRA%G>R>#CRB#L[%>BRC%LCRDP2P111@0P7C519C8331D80%02f6RE%20'7%O=RF%O?R?'jRG'6f9RHf8RIPEf7RJ,1@RKP2P1P0P7GaPHPI%M19K@Kg01L6RK#?RLC5PBP1P211>3R>C:%HBRM58B,9C53DPA11@IRN%M25K@f;ROf:RPP4PLC5PBPEPJP>C:=8BM,9CRQ53DX?AP41F@N%22'7,1@RA1ZN2EEPPPHPAPLC5PBP2PEP>C:=8BM,9C53DP611@H,F@f<R2PO%2JRA,74,1@PLC5PBPJPIP>C:=8BM,9C53DXG6P4PH1DEI%2ERC%2IRM'6RBPEPC1=6CPIPM1=6MEYP1CXPB%JJ%0A%JP%2P#01WF?163F%0?163G[[%0FRAg00EjRJAVF?8UW0%0G\J^0Ag00FFRA%?LRJ#?,A61A6J1A6K5B65B6g01LU'U%HA38%>AP61T67P8%Q6CP%R6%S6RAP61N63RKg01;4RJ1I6=R=C<,;A%i:R?PAP61I6<R<=h6=g01:MR=1N6F=g6@RFC<,;AP?PAP6PKPJP<C<,;ARJP?PAP9P:P:P;PJP6P<P=PFC<,;AFfC@C@C@1`A;P4P7g00IXRAg00J8R;'=1_47=3A;dA^638C]b9b<b=X26X36%081787/6G%07%00160G'b[[[^26^36P4%22f?P1PIPHO5b8b:b;bBbAb6,cHEEPOPP17HC,1@PLC5=3DQP4b1b1b1W7W0W5W4XC5W@XE5X>6WDWFo"). Qed.
End VP29.

Section VP30. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma nth_app_l : forall {A} (l l' : list A) (d : A) j, (j < length l)%nat -> nth j (l ++ l') d = nth j l d.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP30"] "h01Ah11dh21jh31lh42l'p;1p;2p;6p200R0p101Vop4p710p8P0g01Y2R1p4p710p8P0p101XUp4p710p8P0g01kXR2p4p710p8g008gj10TP1j23Tg01RZj22TP2j61Tf0R2#0f1R1#0f2R3g00oLf4R4f3R5'3,22f5P4P5P3P1P2E1UW2W1W4W3X00o"). Qed.
End VP30.

Section VP31. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma In_nth_neq : forall {A} (l : list A) (x d : A) j, ~ In x l -> (j < length l)%nat -> nth j l d <> x.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["VP31"] "h01xh11Ah21Eh32Hjh42Hnh51dh61jh71lp;1p;3p;2p;4p;5p;6p200R0g01MdR1p4p710p8P0g00M8R2p4p710p8P0g01VoR3p4p710p8P0g01Y2R4p4p710p8P0g01l5R5p4p710p8g008gj18TP1j32Tg01NZj11TP4j23Tg01RZj27TP3j40Tg0011j36TP5j54TP2j65Tf0R2#8f1R5f2R3g00oLf4R4f3R1723#1f5R6/34,75f6R7P7P3P6P1C0;64R8P3f7R3P3P1P7P4C0f8?223X03P3P1P7P4P5D4P6P2E5O1W2%18eW3W4W6W5W0W7X10o"). Qed.
End VP31.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
