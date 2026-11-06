(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_LibTail () := "C47Corelib7Program6Basics4flipI45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec=bv_wrap64_modC13~~~C47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3addc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7LibTail7zbv_modC13~~~C56Stdlib6ZArith6BinInt1Z7add_modC47Corelib4Init5Logic6eq_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C56Stdlib6ZArith6BinInt1Z3subC46Stdlib6ZArith4Zdiv:Zminus_modC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_subC13~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7mul_modC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_mulC13~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7LibTail6word_ZC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7LibTail7vadd_ZZC13~~~C47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7LibTail7vsub_ZZC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7LibTail7vmul_ZZC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26edenotC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_addC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX23env00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_subC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5m_mulC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr05C13~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_xorC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_xorC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop06C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_sltuC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_sltuC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX22evC13~~~I47Corelib4Init9Datatypes3nat00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26adenotC13~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01C35stdpp7tactics<f_equal_helpK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S7u_smallC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26a_baseC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25a_offC13~~~K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3ltbC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC45stdpp9bitvector;definitions9bv_signedK46Stdlib9micromega5Tauto8GFormula0:C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AgentLib?bv_signed_smallC13~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK46Stdlib9micromega5Tauto4kind02I47Corelib4Init9Datatypes6option00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S9w_add_natC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SeqExec7rdn_appC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K45stdpp9bitvector;definitions2bv01C46Stdlib5Lists4List2InC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic4True01I47Corelib4Init5Logic2or00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib<callee_savedC13~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Peano2ltC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymDrive9junk_valsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun7vals_evC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef3nthC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymDrive;nth_map_seqC13~~~C47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9SymDriveX=vals_ev_app_rC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9u64_rangeC13~~~C45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z:mod_uniqueK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z7add_0_rC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_addiwC13~~~K46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7LibTail@v_addiw_id_errnoC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7w_addiwC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr04C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:SymDriveH4?low32_zero_sextC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SeqExec7rdn_nthC13~~~C46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib5Lists4List8app_nth1C46Stdlib5Lists4List6nth_In".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Lemma zbv_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01zh12Hah22b1h32b2h41nh51Hh67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__witp;1p;3p;2p;4p;7p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9g000Nj14Tg0011j32Tg001Kj20Tg0025j3RTg002Yj11Tg003>j1MTg003\j1=Tg004:j2BTg004Wj25Tg0057j28Tg005]j27Tg006Cj2?Tg006kj2>Tg007Gj29Tg007cj3QTg008Gj1PTg008gj1OTg009Gj1NTg009ej1LTg00:Cj1KTg00:nj2<Tg00;Qj3DTg00<4j4CTg00<_j7ETg00=Cj6FTg00=gj2GTg00>Ij2HTg00>cj2ATg00?Oj3ITg00?nj4JTg00@`j3@Tg00AAj1;Tg00BRj66Tg00C0j2:Tg00C_R1f1R0f0R232p=3g00D=R3%42R4%40R5g00D[f2R6#4?202f3R7/061070'3R8[10601062'3%47?260[R9f4#4?276\8AR602P2n2001000000120000000W3W2W4P9^35^24^43P2g00E6#1R3#1#1#1#1#1R4#MR5%=3R3%=4R4'BR9,50R8,85R71850R:P11758R;1856,05,32X01P11750R<1569R=,75/32X01P115891756,32X01P1P815=9/32X011?34g00E[R=/>319=41>=9[[19=3R>g00F9R?AQ340UW119=9\?^1>g00FUR>#P%O>%N1%L1%K1R>g00GAR?g00G`R4P4g00H@R@P>P?P4P4P@P11<13=D15g00H`1<1=CCg00IGFEEF1G>@P2P6g00IgR@g00JGR>'H1A26=2@>dAI1=0CJb7b:b;A219=g00Jg[P2b6b8b99@09P<%;0E6P;%;8E6105:1:50E610571:58E6O4b5X01o"). Qed.

Lemma vadd_ZZ : forall x y, v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01zh12Hah27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__with81bh91xh:1yp;1p;2p;3p;4p;7p;6g002Yj13Tg003>j1TTg005]j26Tg000Nj1CTg0057j20Tg001Kj2>Tg00KDj22Tg0011j31Tg003\j1<Tg004:j2DTg004Wj24Tg00Kaj18Tg006Cj2@Tg006kj2?Tg007Gj27Tg007cj3STg008Gj1RTg008gj1QTg009Gj1PTg009ej1OTg00:Cj1NTg00:nj2;Tg00;Qj3MTg00<4j4LTg00<_j7KTg00=Cj6ETg00=gj2FTg00>Ij2GTg00>cj2HTg00?Oj3ITg00?nj4JTg00Lkj4BTg00MLj69Tg00AAj1=Tg00BRj65Tg00C0j2:Tg00Mhj2ATg00C_R0P0g00E6#3R1#3#3#3#3#3R2#TR3f1R4'6R5%C3R6f0R71034R8,>3R9'2,03f2R:/24,03R;31X00P01637R<163:/27,03=16;X00P0%<1R1%<2R2'DR=,44R>1275,03=16;X00P0147=R?14:=/27,03=16;X00P612>?R?/4=R>,03A167;X86P01247R@/4=1037RA=16;X00%8@P>P4P7P=1@12g00E[R>/?117>21?>=[[17>1R;g00F9RBAS124UW117>=\B^1;g00FUR;#R%Q;%P0%O0%N0R;g00GARBg00G`R2P2g00H@RCP;PBP2P2PCP01;01=M03g00H`1;0>CLg00IGFKEE1F;CP7P:g00IgRCg00JGR;'G1H7:=1C;dAI0>4CJb3b6b7A10=>g00Jg[P7b2b4b5CBE9103?%8?E9P<%=7E5P5%=4E51>3A1:37E5P91:34E51A8A103@516eX:0W9o"). Qed.

Lemma vsub_ZZ : forall x y, v_sub (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01zh11bh21xh31yp;1p;2p;3p;6g002Yj13Tg003>j1ATg005]j26Tg000Nj1>Tg0057j20Tg001Kj29Tg00O1j22Tg0011j31Tg003\j18Tg004:j2?Tg004Wj24Tg00Kaj17Tg00ONj3=Tg00MLj6<Tg00AAj1;Tg00BRj65Tg00C0j2:Tg00Onj2@Tg00C_R0P0g00E6#3R1#3#3#3#3#3R2#AR3f1R4'6R5%>3R6f0R71034R8,93R9'2,03f2R:/24,03R;31X00P01637R<163:/27,03=16;X00P0%81%82'?R2,44R11275,03=16;X00P01472R=14:2/27,03=16;X00P6121=R=/42R1,03A167;X16P01247R:/421037R>=16;X00%7:P1A=472E<103=%7=E<P<%;7E5P5%;4E5193>1:37E5P91:34E51@8>103:516eX30W2o"). Qed.

Lemma vmul_ZZ : forall x y, v_mul (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x * y).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01zh12Hah27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__with81bh91xh:1yp;1p;2p;3p;4p;7p;6g002Yj13Tg003>j1TTg005]j26Tg000Nj1CTg0057j20Tg001Kj2>Tg00Q7j22Tg0011j31Tg003\j1<Tg004:j2DTg004Wj24Tg00Kaj18Tg006Cj2@Tg006kj2?Tg007Gj27Tg007cj3STg008Gj1RTg008gj1QTg009Gj1PTg009ej1OTg00:Cj1NTg00:nj2;Tg00;Qj3MTg00<4j4LTg00<_j7KTg00=Cj6ETg00=gj2FTg00>Ij2GTg00>cj2HTg00?Oj3ITg00?nj4JTg00QTj4BTg00MLj69Tg00AAj1=Tg00BRj65Tg00C0j2:Tg00R5j2ATg00C_R0P0g00E6#3R1#3#3#3#3#3R2#TR3f1R4'6R5%C3R6f0R71034R8,>3R9'2,03f2R:/24,03R;31X00P01637R<163:/27,03=16;X00P0%<1R1%<2R2'DR=,44R>1275,03=16;X00P0147=R?14:=/27,03=16;X00P612>?R?/4=R>,03A167;X86P01247R@/4=1037RA=16;X00%8@P>P4P7P=1@12g00E[R>/?117>21?>=[[17>1R;g00F9RBAS124UW117>=\B^1;g00FUR;#R%Q;%P0%O0%N0R;g00GARBg00G`R2P2g00H@RCP;PBP2P2PCP01;01=M03g00H`1;0>CLg00IGFKEE1F;CP7P:g00IgRCg00JGR;'G1H7:=1C;dAI0>4CJb3b6b7A10=>g00Jg[P7b2b4b5CBE9103?%8?E9P<%=7E5P5%=4E51>3A1:37E5P91:34E51A8A103@516eX:0W9o"). Qed.

Lemma word_Z : forall w : word, w = Z_to_bv 64 (bv_unsigned w).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01wp;1p;2p;4g002Yj10Tg003>j16Tg000Nj12Tg001Kj21Tg0057j25Tg00S>j24Tg00T0j43Tg00E6#0#0#0#0#0#0#6R0#2R1P1f0R1,10,50P11401C3W0o"). Qed.

(* [comment removed for export] *)
Lemma vadd_wZ : forall (w : word) y, v_add w (Z_to_bv 64 y) = Z_to_bv 64 (bv_unsigned w + y).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01yh15lemmah21wh31xp;1p;2p;3p;4p;:p;9g002Yj10Tg003>j1BTg000Nj19Tg001Kj23Tg0057j21Tg0011j3<j1;Tg00TLj18Tg00MhR0j22Tg00U<j44Tg00Ucj17Tg00VRj45Tg00WIj3:Tg00X?j26Tg00Xkl:ATg00KDj2@Tg00YXl9=Tg00ZRj1>Tg00[[j2?Tg00E6#0#0#0#0#0#0#BR1#9R2g00C_f1R31313R4,115<2P2%;2R5%82f2R61113R7'21316R8,11R9/27P2^02R:^32R;P2P:P5P2P2P5P5C4R<C4R=P2P:P<P2P2P5%72C5C59:;=P0P6P9f0R9P7P71627M:A1@83,11R1P11621M9=W1%>31?49O2W0W2o"). Qed.
Lemma vadd_Zw : forall x (w : word), v_add (Z_to_bv 64 x) w = Z_to_bv 64 (x + bv_unsigned w).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h05lemmah11wh21xh31yp;1p;2p;3p;4p;;p;9g002Yj10Tg003>j1CTg000Nj19Tg001Kj23Tg0057j21Tg0011j3<j1;Tg00TLj18Tg00MhR0j22Tg00U<j44Tg00Ucj17Tg00VRj45Tg00WIj3:Tg00Xkj4BTg00X?j26Tg00\el;ATg00KDj2=Tg00YXl9>Tg00ZRj1?Tg00[[j2@Tg00C_g00E6#0#0#0#0#0#0#CR1#9R2f0R31313R4,115<2P2%;2R5%82f2R6,11R7f1R8'21318R9,11R:,27P2P2^32R;P5P2P2P5P5C4R<P0P;\2R=P2P;P5P<C4R>P2P;P<P2P2P5%72C5C59:=>P0CBP71627P8P:P3M;A1=69,11R1P11621M9>W0%?31@84O2W1W2o"). Qed.
Lemma vadd_ww : forall (w w' : word), v_add w w' = Z_to_bv 64 (bv_unsigned w + bv_unsigned w').
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01wh12w'p;1p;2g002Yj10Tg003>j16Tg000Nj12Tg001Kj21Tg00KDj25Tg0057j24Tg00>Ij23Tg00E6#0#0#0#0#0#0#6R0#2R1f1,10f0,10'5,40,31X11W0o"). Qed.
Lemma vsub_wZ : forall (w : word) y, v_sub w (Z_to_bv 64 y) = Z_to_bv 64 (bv_unsigned w - y).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01yh15lemmah21wh31xp;1p;2p;3p;4p;:p;9g002Yj10Tg003>j1BTg000Nj19Tg001Kj23Tg0057j21Tg0011j3<j1;Tg00TLj18Tg00OnR0j22Tg00U<j44Tg00Ucj17Tg00VRj45Tg00WIj3:Tg00X?j26Tg00Xkl:ATg00O1j2@Tg00YXl9=Tg00ZRj1>Tg00]`j2?Tg00E6#0#0#0#0#0#0#BR1#9R2g00C_f1R31313R4,115<2P2%;2R5%82f2R61113R7'21316R8,11R9/27P2^02R:^32R;P2P:P5P2P2P5P5C4R<C4R=P2P:P<P2P2P5%72C5C59:;=P0P6P9f0R9P7P71627M:A1@83,11R1P11621M9=W1%>31?49O2W0W2o"). Qed.
Lemma vsub_Zw : forall x (w : word), v_sub (Z_to_bv 64 x) w = Z_to_bv 64 (x - bv_unsigned w).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h05lemmah11wh21xh31yp;1p;2p;3p;4p;;p;9g002Yj10Tg003>j1CTg000Nj19Tg001Kj23Tg0057j21Tg0011j3<j1;Tg00TLj18Tg00OnR0j22Tg00U<j44Tg00Ucj17Tg00VRj45Tg00WIj3:Tg00Xkj4BTg00X?j26Tg00\el;ATg00O1j2=Tg00YXl9>Tg00ZRj1?Tg00]`j2@Tg00C_g00E6#0#0#0#0#0#0#CR1#9R2f0R31313R4,115<2P2%;2R5%82f2R6,11R7f1R8'21318R9,11R:,27P2P2^32R;P5P2P2P5P5C4R<P0P;\2R=P2P;P5P<C4R>P2P;P<P2P2P5%72C5C59:=>P0CBP71627P8P:P3M;A1=69,11R1P11621M9>W0%?31@84O2W1W2o"). Qed.
Lemma vmul_wZ : forall (w : word) y, v_mul w (Z_to_bv 64 y) = Z_to_bv 64 (bv_unsigned w * y).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01yh15lemmah21wh31xp;1p;2p;3p;4p;:p;9g002Yj10Tg003>j1BTg000Nj19Tg001Kj23Tg0057j21Tg0011j3<j1;Tg00TLj18Tg00R5R0j22Tg00U<j44Tg00Ucj17Tg00VRj45Tg00WIj3:Tg00X?j26Tg00Xkl:ATg00Q7j2@Tg00YXl9=Tg00ZRj1>Tg00^jj2?Tg00E6#0#0#0#0#0#0#BR1#9R2g00C_f1R31313R4,115<2P2%;2R5%82f2R61113R7'21316R8,11R9/27P2^02R:^32R;P2P:P5P2P2P5P5C4R<C4R=P2P:P<P2P2P5%72C5C59:;=P0P6P9f0R9P7P71627M:A1@83,11R1P11621M9=W1%>31?49O2W0W2o"). Qed.
Lemma vmul_Zw : forall x (w : word), v_mul (Z_to_bv 64 x) w = Z_to_bv 64 (x * bv_unsigned w).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h05lemmah11wh21xh31yp;1p;2p;3p;4p;;p;9g002Yj10Tg003>j1CTg000Nj19Tg001Kj23Tg0057j21Tg0011j3<j1;Tg00TLj18Tg00R5R0j22Tg00U<j44Tg00Ucj17Tg00VRj45Tg00WIj3:Tg00Xkj4BTg00X?j26Tg00\el;ATg00Q7j2=Tg00YXl9>Tg00ZRj1?Tg00^jj2@Tg00C_g00E6#0#0#0#0#0#0#CR1#9R2f0R31313R4,115<2P2%;2R5%82f2R6,11R7f1R8'21318R9,11R:,27P2P2^32R;P5P2P2P5P5C4R<P0P;\2R=P2P;P5P<C4R>P2P;P<P2P2P5%72C5C59:=>P0CBP71627P8P:P3M;A1=69,11R1P11621M9>W0%?31@84O2W1W2o"). Qed.

(* [comment removed for export] *)
Lemma ed_add : forall E a b, edenot E (EAlu ALU_ADD a b) = v_add (edenot E a) (edenot E b).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01Eh11ah21bp;2p;1p;3g00`4j21Tg00aBj27Tg002Yj10Tg003>j12Tg000Nj16Tg00bMj35Tg00Mhj24Tg0011j33Tg00c[g00dhR0f2R1f1R2'1R3f0R4,11R5'7g00E6#0#0#0#0#0#0#2#6g00f6?524,11143533eX20W1W0o"). Qed.
Lemma ed_sub : forall E a b, edenot E (EAlu ALU_SUB a b) = v_sub (edenot E a) (edenot E b).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01Eh11ah21bp;2p;1p;3g00`4j21Tg00fbj27Tg002Yj10Tg003>j12Tg000Nj16Tg00bMj35Tg00Onj24Tg0011j33Tg00c[g00dhR0f2R1f1R2'1R3f0R4,11R5'7g00E6#0#0#0#0#0#0#2#6g00gm?524,11143533eX20W1W0o"). Qed.
Lemma ed_mul : forall E a b, edenot E (EMd M_MUL a b) = v_mul (edenot E a) (edenot E b).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01Eh11ah21bp;2p;1p;3g00`4j21Tg00hYj27Tg002Yj10Tg003>j12Tg000Nj16Tg00ibj35Tg00R5j24Tg0011j33Tg00c[g00dhR0f2R1f1R2'1R3f0R4,11R5'7g00E6#0#0#0#0#0#0#2#6g00k0?524,11143533eX20W1W0o"). Qed.
Lemma ed_xor : forall E a b, edenot E (EAlu ALU_XOR a b) = v_xor (edenot E a) (edenot E b).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01Eh11ah21bp;2p;1p;3g00`4j21Tg00k\j27Tg002Yj10Tg003>j12Tg000Nj16Tg00bMj35Tg00lgj24Tg0011j33Tg00c[g00dhR0f2R1f1R2'1R3f0R4,11R5'7g00E6#0#0#0#0#0#0#2#6g00n0?524,11143533eX20W1W0o"). Qed.
Lemma ed_sltu : forall E a b, edenot E (EAlu ALU_SLTU a b) = v_sltu (edenot E a) (edenot E b).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01Eh11ah21bp;2p;1p;3g00`4j21Tg00n\j27Tg002Yj10Tg003>j12Tg000Nj16Tg00bMj35Tg00ohj24Tg0011j33Tg00c[g00dhR0f2R1f1R2'1R3f0R4,11R5'7g00E6#0#0#0#0#0#0#2#6g0112?524,11143533eX20W1W0o"). Qed.
Lemma ed_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01Eh11zp;1p;2g002Yj10Tg003>j14Tg000Nj12Tg0057j21Tg00>Ij23Tg00c[g00C_g00E6#0#0#0#0#0#0#4R0#2f0,10'3W1W0o"). Qed.
Lemma ed_var : forall E n, edenot E (EVar n) = ev E n.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_1"] "h01Eh11np;1p;2g002Yj10Tg003>j14Tg000Nj12Tg011^j21Tg00>Ij23Tg00c[g012hg00E6#0#0#0#0#0#0#4#2f1f0'1'3W1W0o"). Qed.
End FPX_1.


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
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Lemma adenot_off_shift : forall E b k d k',
  (k' = k + d)%Z ->
  (0 <= bv_unsigned (edenot E b) + k)%Z -> (bv_unsigned (edenot E b) + k < 2 ^ 64)%Z ->
  Z_to_bv 64 (bv_unsigned (adenot E (SA b k)) + d) = adenot E (SA b k').
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_2"] "h04__x1h14__x2h22Hah37__arithh44__ffh56__sat2h66__sat3h78__varmaph85__with94__x3h:2k'h;1Eh<1Hh=2H0h>2H1h?1bh@1dhA1khB1zp;2p;3p;1p;4p;8p;7p;6g00KDj20Tg0011j35Tg002Yj17Tg003>j1KTg00`4j24Tg001Kj2;Tg003\j1@Tg004:j2QTg006kj26Tg000Nj1ITg013Gj2:Tg014Vj29Tg0057j22j1^Tg00>Ij2DTg006Cj2ZTg007cj3YTg008Gj1XTg008gj1WTg015dj2BTg016Bj4ATg009ej1VTg00:Cj1UTg016`j2<Tg017Cj38Tg017fj1RTg00<4j4=Tg00=gj2PTg00>cj2JTg00?Oj3LTg00?nj4MTg018Kj8NTg009Gj1OTg00:nj2?Tg00;Qj3HTg018hj1STg019Jj7TTg00D[j2`Tg019nj2_Tg00BRj6ETg01;Cj1CTg01<Qj1FTg007Gj2]Tg00<_j7\Tg01=^j8[Tf2R0f1R1';f0R2'0p=1g00E[R3/]2p=3P1g00GAR4g00G`R5P5g00H@R6P2g00IGF\p=>f3R7P4P5P5P6P0P1P2G[p=Gg00c[g00dhg00C_R810019582P81070g00E6R9#7R:#7#7#7#7#7R;#KR<f6R=f5R>'4f4R?31R@#3f7RA/4=,;<RB/0>RC%@:RD%@;R;'QRE'6%I<RFf8RG1:A='9=1<>,2<1:A0,9G35[[X:814>?=1<7#316@EP8PC102>,2<14GA10=>51<,2<55FXB8P8PF%^<R@P@10C?10>?RH,0BPF\8/D@1ZD;R@163D%3;163E[[RB%3DRIg00F9RJAYD;1UW2R;%3E\J^2IRIg00FURJ#XRK%WJRJP81B80RLP11B87CA%V8RM%U8RNP81<89RO1<8:R:588RP%R9,<8R9588g00H`A88:9988OC='>1PN6ROP2P0g00IgR9g00JGR:'D1J20=59:dAL831CMR:b4b7b8X08X18X981021R9/001010RQ,02558^08^18^98P2PAPGf:f9'4,;<RRO3b3b5b6GN12<C,;<P@PBP;PIPKPJP8PLP1%O8CAPMPNP8PPg01>B1?8D=H8<C=,>NRD%S5RMPNP81?83g01>iPPC=,>NRPPMPNP4P5P5P6PPPDFTCGCGPOP:b4b7b8X08X18169E%3Q1007R0#3160E'`[[^08^18P2PGPRP7P?O4b3b5b6,_CEE1:=>R>#C,4A%F>51<,2<=1<?,2<1:=HRH#C,4A%FH51<,2<55Fe19A>=1<?,2<19AH55FeW>W=P1P2EEW<X:8X@8WAW?W;o"). Qed.

(* [comment removed for export] *)
Lemma eqb_ZZ : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_2"] "h02Hah17__arithh26__sat1h36__sat2h44__x1h51zh64__ffh78__varmaph85__with91ah:1bp;2p;1p;3p;4p;7p;8p;6g007Gj21Tg002Yj10Tg003\j1=Tg004:j2BTg006kj24Tg00D[j2<Tg003>j1LTg0057j29Tg001Kj25Tg01?Pj22Tg0011j33Tg00>Ij2>Tg006Cj2?Tg007cj3RTg008Gj1QTg008gj1PTg015dj2OTg009ej1NTg00:Cj1MTg00:nj2;Tg016`j2KTg00<4j46Tg00;Qj3FTg019Jj7ETg018hj1DTg01=^j8GTg00=gj2HTg00>cj2CTg00?Oj3ITg00?nj4JTg019nj27Tg00BRj68Tg01?mj3ATg00<_j7@Tf1R0g00GAR1g00G`R2P2g00H@R3f0R4g00IGF@p=:g00C_R5g00E[R6/10g00E6R7#0R8#=R9%08#0#0#0#0R8#=R:'BR;,40'<R<P5f3R=g00IgR>%L8R8198=R?'5R@,24f4RA/2=RB33X55P5f2RC12A4=3>BX5512=CRB,>>198CRD,581?9:RE1469116:146;[[RF1169RGg00F9RHAR9:0UW0R:116;\H^0GRGg00FURH#Q%PH1O50%N5%M5RHP1P2P2P3PHP1P2P2P3P51;56g01>i1K57R7C6,:HP5P7g01>B1;59=F58C6,:HFER9%D2P9GG1HH3P4PCg00JGRH,>>1C4C=3>HdAI560CJb6b7b8X45R01164144;'<P<[^45R;P4f5P=O2b1b2b3,7CE8P@PEPFP:PGP0P;P4f6PAO2b1b2b3,7=E8AA8?D=3>BeV<UX:5W9o"). Qed.
Lemma ltu_ZZ : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.ltb a b.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_2"] "h02Hah17__arithh26__sat1h36__sat2h44__x1h51zh64__ffh78__varmaph85__with91ah:1bp;2p;1p;3p;4p;7p;8p;6g007Gj21Tg002Yj10Tg003\j1=Tg004:j2BTg006kj24Tg00D[j2<Tg003>j1LTg0057j29Tg001Kj25Tg01@Zj22Tg0011j33Tg00>Ij2>Tg006Cj2?Tg007cj3RTg008Gj1QTg008gj1PTg015dj2OTg009ej1NTg00:Cj1MTg00:nj2;Tg016`j2KTg00<4j46Tg00;Qj3FTg019Jj7ETg018hj1DTg01=^j8GTg00=gj2HTg00>cj2CTg00?Oj3ITg00?nj4JTg019nj27Tg00BRj68Tg01A7j3ATg00<_j7@Tf1R0g00GAR1g00G`R2P2g00H@R3f0R4g00IGF@p=:g00C_R5g00E[R6/10g00E6R7#0R8#=R9%08#0#0#0#0R8#=R:'BR;,40'<R<P5f3R=g00IgR>%L8R8198=R?'5R@,24f4RA/2=RB33X55P5f2RC12A4=3>BX5512=CRB,>>198CRD,581?9:RE1469116:146;[[RF1169RGg00F9RHAR9:0UW0R:116;\H^0GRGg00FURH#Q%PH1O50%N5%M5RHP1P2P2P3PHP1P2P2P3P51;56g01>i1K57R7C6,:HP5P7g01>B1;59=F58C6,:HFER9%D2P9GG1HH3P4PCg00JGRH,>>1C4C=3>HdAI560CJb6b7b8X45R01164144;'<P<[^45R;P4f5P=O2b1b2b3,7CE8P@PEPFP:PGP0P;P4f6PAO2b1b2b3,7=E8AA8?D=3>BeV<UX:5W9o"). Qed.
Lemma lts_ZZ : forall a b, (0 <= a < 2 ^ 63)%Z -> (0 <= b < 2 ^ 63)%Z ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.ltb a b.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_2"] "h04__x1h12Hah27__arithh36__sat0h46__sat1h54__ffh68__varmaph75__with84__x2h91zh:2Hbh;1ah<1bp;2p;1p;3p;4p;7p;6p;8g007Gj24Tg002Yj10Tg003\j1<Tg017fj12Tg004:j2VTg006kj25Tg00D[j2=Tg003>j17Tg0057j2:Tg01Adj28Tg01@Zj21Tg0011j33Tg006Cj2CTg007cj3UTg008Gj1TTg008gj1STg015dj2>Tg009Gj1QTg016Bj4PTg009ej1NTg00:Cj1MTg016`j29Tg00<4j46Tg00<_j7;Tg01BLj6LTg00=gj2KTg00>Ij2JTg00>cj2HTg00?Oj3GTg00?nj4ITg00:nj2@Tg00;Qj3FTg019Jj7ETg018hj1DTg01=^j8OTg01C0j2ATg00BRj6BTg01DCj3RTf1R0g00GAR1g00G`R2P2g00H@R3f0R4g00IGR5F;p=?g00C_R6g00E[R7/40g00E6R8#0R9#<R:%28#2#2#2#2R;#<R<'VR=,50'=R>P6f3R?g00IgR@%09#0#0#0#0#7RA1:A?RB'8RC,14f4RD/1?RE33X96P6f2RF11D4=3@EX961C:<RE157:147<157=[[RG147:RHg00F9RIAU:<0UW1R<147=\I^1HRHg00FURI#TRJ%SIRIP61>6FP0%Q6CP%N6RK%M6RLP1P2P2PLP1P2P2g01E0P61968R8g01>BRM1969C6P5F;R5P5EL1KL3R5P4PFg00JGR9,J@1H4F=3@9dAG670CIR9b5b6b7X06X861140RN=3@N^06^86P4f5RNf6ROO2b2b3b41:AFRP,8APEPGP<PHPJPI1>60PKPLP1P2P2P3PLP1P2P2P3P61@67g01>iP8C6,?LP6P8PM1@6:%7;5F6C6,?LFERL%D2PLGOP5P9b5b6b7X06R91474154='=P>[^06R=P4PNP?O2b2b3b4,AFEBPCPEPGP<PHP9P=P4POPDO2b2b3b4,A?EBARABP11?F53@eX:>W1X<6W;o"). Qed.
End FPX_2.


(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (u_small z) by lia
      end
  end.
Section FPX_3. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Lemma rdn_app_Z : forall segs m a n1 n2 b1 b2,
  rdn segs m (Z_to_bv 64 a) n1 = Some b1 ->
  rdn segs m (Z_to_bv 64 (a + Z.of_nat n1)) n2 = Some b2 ->
  (0 <= a)%Z -> (a + Z.of_nat n1 < 2 ^ 64)%Z ->
  rdn segs m (Z_to_bv 64 a) (n1 + n2) = Some (b1 ++ b2).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_3"] "h02Hah14__x1h24__x2h32H1h42H2h52Hnh67__arithh74__ffh86__sat3h96__sat4h:8__varmaph;5__with<1ah=1bh>2b1h?2b2h@4cstrhA1mhB2n1hC2n2hD4segshE1zp;1p;2p;4p;3p;7p;6p;9p;8g008gj1=Tg002Yj11Tg003>j1@Tg000Nj1DTg01EPj1FTg0057j23Tg01F2j48Tg01G9j2ATg0011j34Tg01G[j12Tg00KDj25Tg003\j1CTg004:j2eTg006kj26Tg001Kj2XTg01H;j1WTg006Cj2UTg007cj3TTg01H`j1:Tg01I?j2<Tg01Ihj3BTg01JQj2QTg008Gj1PTg01K=j3OTg015dj2NTg009Gj1MTg016Bj4LTg009ej1KTg00:Cj1JTg00:nj2?Tg016`j2>Tg00<4j47Tg018hj1ITg017Cj3HTg00;Qj3RTg019Jj7GTg00=gj2STg00>Ij2dTg00>cj2cTg00?Oj3bTg00?nj4]Tg00D[j2\Tg019nj2YTg00BRj6ETg01K]j1ZTg01LXj3[Tg01M=j2VTg01NTl9^Tg007Gj2_Tg00<_j7`Tg01=^j8aTg00E[R0f0R1'_p=0f1R2g00GAR3g00G`R4P4g00H@R5P1g00IGF`p=9f3R6P3P4P4P5f2R7P2P1Gap=;g01O^#=g00E6R8#1R9#1#1R:#1#1#1R;#@R<#DR=%@:#DR:#F[g00C_R>g012hR?%=:R:%F:R@f6RAf5RBf4RC,3<P6C81A:2RD34f7REPA%2C,5B,3<P6C8=4@D%0A%2A,5E%C9RD%C;R;'eRF'6f:RGf9PEPAf8RA,3<RHPBPCP6P=1X<HRI%2ERJ'5,3<f;RKPGP1PEC81A:BRL54@X==P>PAPKPG%2A,51,3<PEC8=4@LXE>P7PI%WE%0J1UD;160D%0;160F[[%0DRJg00F9RIATD;2UW0%0F\I^0Jg00FURJg01P]RI#:#:R;#:,<>1<>;1<>I5B>5B>g01Q<'Q%PJ3O%=JP>1N>7P2%M>CL%K>%J>RJP>1?>0RIg01>iR;1>>9R9C7,9J%I4RLPJP>1>>8R8=H>9g01>BR91?>D=R><RDC7,9JPLPJP>PIP;P8C7,9JR;PLPJP3P4P4P5P;P>P8P9PDC7,9JFGC;C;C;1SJ5P1P7g00IgRJg00JGR5'd1c17=4J5dAb>02C]b7b:b;X1>X2>%021527/6F%07%06166F'\[[[^1>^2>P1%2Kf<P6PCPBO5b6b8b9b@,YAEE%ZE9[<H1VHEEEM9^W5W0W4W3X?:W>XC?WBW<WAWDo"). Qed.

Lemma callee_saved_no0 : ~ In (0%bv : reg) callee_saved.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_3"] "p'0h03Hinh11Hh21ei001zp;1p;3p;2p;6g002Yj18Tg017fj19Tg003>j1>Tg000Nj1=Tg01Qhj3;Tg008Gj1?Tg01K=j34Tg01RKj30Tg0011j31Tg001Kj1<j22Tg01Rbj2CTg01SAj1:Tg003\j1BTg01SZj6ATg00MLj6@Tf1R0f0R1#Bg01T7R23;p=5f4g00C_R3f3R4f2R5P0P1EAp=7A1301p=6P3P4P5P2P0P1E@p=3g00E6R0#8R5#9R4#>R6#=R7g00E[=;62R21560R81565R9%90R0,56R:%85R5,56R;%85,56R<%95R5,56R=%85,56R>%95,56R5%84R?#8,56R@%9?,56R?%94R4#8,56RA%94,56R4%80R0#8RB#8,56RC%9B,56RB%90R0#8,56RD%90,56R0%?7RE547RF547RG547RH547RI547RJ547RK547RL547RM547RN547RO547RP547RQ547RR547RS547RT54730RUg01TSRVA1782RWA072TRTg00JgRXP1P7%<6RYP8P2P1D71268R81262RZ'6P8P3p-0P1PXg00F9PXn011000003001000010000X23R3PZP1C3PX1CX1R8b1b0X0WP1O1PVA1792RWA072SRSPXP1P7PYP9P2P1D71269R9/6ZP9P3PZP1C3PXP8b1b0X0WP1O1PVA17:2RWA072RRRPXP1P7PYP:P2P1D7126:R:/6ZP:P3PZP1C3PXP8b1b0X0WP1O1PVA17;2RWA072QRQPXP1P7PYP;P2P1D7126;R;/6ZP;P3PZP1C3PXP8b1b0X0WP1O1PVA17<2RWA072PRPPXP1P7PYP<P2P1D7126<R</6ZP<P3PZP1C3PXP8b1b0X0WP1O1PVA17=2RWA072OROPXP1P7PYP=P2P1D7126=R=/6ZP=P3PZP1C3PXP8b1b0X0WP1O1PVA17>2RWA072NRNPXP1P7PYP>P2P1D7126>R>/6ZP>P3PZP1C3PXP8b1b0X0WP1O1PVA1752RWA072MRMPXP1P7PYP5P2P1D71265R5/6ZP5P3PZP1C3PXP8b1b0X0WP1O1PVA17@2RWA072LRLPXP1P7PYP@P2P1D7126@R@/6ZP@P3PZP1C3PXP8b1b0X0WP1O1PVA17?2RWA072KRKPXP1P7PYP?P2P1D7126?R?/6ZP?P3PZP1C3PXP8b1b0X0WP1O1PVA17A2RWA072JRJPXP1P7PYPAP2P1D7126ARA/6ZPAP3PZP1C3PXP8b1b0X0WP1O1PVA1742RWA072IRIPXP1P7PYP4P2P1D71264R4/6ZP4P3PZP1C3PXP8b1b0X0WP1O1PVA17C2RWA072HRHPXP1P7PYPCP2P1D7126CRC/6ZPCP3PZP1C3PXP8b1b0X0WP1O1PVA17B2RWA072GRGPXP1P7PYPBP2P1D7126BRB/6ZPBP3PZP1C3PXP8b1b0X0WP1O1PVA17D2RWA072FRFPXP1P7PYPDP2P1D7126DRD/6ZPDP3PZP1C3PXP8b1b0X0WP1O1PVA1702RVA072EREPXP1P7PYP0P2P1D71260R0/6ZP0P3PZP1C3PXP8b1b0X0VP1O1P1X0EP1O1n200100000021000010000X0FP1O1n200100000021000011000X0GP1O1n200100000021000011000X0HP1O1n200100000021000011000X0IP1O1n200100000021000011000X0JP1O1n200100000021000011000X0KP1O1n200100000021000011000X0LP1O1n200100000021000011000X0MP1O1n200100000021000011000X0NP1O1n201100000021000011000X0OP1O1n201100000021000011000X0PP1O1n201100000021000011000X0QP1O1n201100000021000011000X0RP1O1n201100000021000011000X0SP1O1n201100000021000011000X0TP1O1n201100000021000011000W0%:UeP2P7eg01Tm507#:eo"). Qed.

(* [comment removed for export] *)
Lemma vals_ev_junk : forall vals R i, (i < 32)%nat ->
  vals_ev (vals ++ junk_vals R) (length vals + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_3"] "h01ih12Hih21Rh31bh44valsp;1p;2p;3p;4p;6g002Yj11Tg003>j18Tg000Nj1=Tg008gj1:Tg017fj1HTg01VAj2ETg01Vmj2<Tg01WEj1;Tg01XRj26Tg01G[j14Tg0057j23Tg01Y[j25Tg0011j39Tg00>Ij2GTg01Zcj2FTg01[?j4DTg01[[j4@Tg01\7j6?Tg00BRj67Tg01]Fj3>Tg01]cj2ATg01^Cj2BTg01^Zj3CTg01H`j12Tf0R0#2#2#2#2p=0g00E6#1R1#1#1#1#1#1#8R2#=R3#:%H1#8R1/E3g012hR4g01P]R5#0#0#0#0#0#0#0#0R6,<0P3f2R7#;R8f1R9'6R:f3R;%47,31'59930X33R<P3%49,31,57R7P<1G37P3P9P4P3%40,31,5;X04R41F56CDg00E[,32R2C@P3P4P9P6P2P0E?E7A93:7eA>3;81A3;/B9'6AC;89E7W1W0W2W4o"). Qed.

(* [comment removed for export] *)
Lemma v_addiw_id_errno : forall x : word,
  (2 ^ 64 - 4095 <= bv_unsigned x)%Z -> v_addiw x 0 = x.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_3"] "h04__x1h11Hh22Hah32H0h47__arithh54__ffh64__p1h76__sat0h86__sat1h98__varmaph:5__with;6__sat2h<6__sat3h=1zh>6__sat4h?6__sat5h@2b1hA2b2hB1nhC2HrhD2HxhE1xp;1p;2p;3p;4p;6p;7p;8g002Yj1:Tg003>j1KTg000Nj1;Tg003\j1=Tg004:j2LTg017fj1HTg00O1j23Tg001Kj20Tg007Gj29Tg01_lj1UTg006kj21Tg00D[R0j26Tg01a9j2RTg0057j2QTg0011j38Tg0025j3_Tg005]j2^Tg004Wj2<Tg00KDj24Tg006Cj2GTg007cj3FTg01TSj2ATg008Gj1[Tg008gj1ZTg015dj2YTg009ej1XTg00:Cj1WTg016`j2VTg00:nj2BTg00;Qj3ETg00<4j4>Tg018hj1TTg01a`j3DTg017Cj3JTg01bCj6nTg00=gj2mTg00>Ij2lTg00>cj2kTg00?Oj3iTg00?nj4hTg00Q7j2NTg01bgj3PTg01cJj6OTg01cnj1aTg00T0j4`Tg00MLj6bTg00AAj1cTg00BRj6ITg00C0j2dTg01dLj1eTg01dmj2]Tg00<_j7fTg019Jj7gTg01f8j7\Tg01=^j8jTf0R1#H#Hp=?g00E[R2/91p=2g00C_R3f1R4;81p=5P4g00GAR5g00G`R6P6g00H@R7P1g00IGFfp=7P3P4g01>iP1C>p=Cf2R8P5P6P6P7P4P1Fgp=MP8P5P6P6P7P4P1F\p=Sf3R9P5P6P6P7P8P4P1Gjp=@g00E6R:#:R;#:#:#:#:R<#:R=#KR>#;R?%=;R;%==R='LR@%?:#?RA#H#?#?#?#=RB'3RC10>1'9%U410>4RD#211D@'6P310>8RD%K<RE/R1,Q>=8?9X=3g00D=RF%;1RG%;4RHP0%;8?84110981094'5RI[10841081'5%;9?884[RJf4RK#;?898\IA_841P1n2001000000120000000WAW@WBPJ^AH^@G^BFP1P>10>9RF,RERG,Q>RHP9P31^>GRJ10>KRI,51X=3RLP31<G@RMPL%=ARL,L;RN,4FRO%=<R<,L;RPPP13O@RQ1G;<RR112;RS%2<112P[[RT%2;RUg00F9RVAF;<4UW2R<%2P\V^2URW1G;LRX%2L112N[\SRYAF;L4VVX2URL%2N\V^2URZ1G;=R[%2=112@[\SRSAF;=4VVX2UR=%2@\V^2URUP0f9,0>RV#2R\11V@R]f:R^,0>R_/4NR`/3@Ra#211aP'611Pa19a2'6'Af7Rbf;,0>Rc#2Rdf<,0>/1@Rep-0Rfg00FURg#[Rh%ZgRg1Y34Ri%X3Rj%W3RkP31V3:Rlg01>BRm1B3;R;=E3>RnC>,7kRo%T6RpPk1B3B9D3n/Cl,7kRBPp1B32Rq%KA9E3;RA9J3lRr=D3nRs'C,7kP3PsPmAE3;ER;C>,7k5MkPkP5P6P6P7P9EnR65SkC@C@1mk7R7P1P8g00IgR5g00JGRE'l1k18=85EdAi324ChREb5b9b:X03W6111@R519C4RC148N/3@Rm#211mP'6/A9[[^03^6fP1f>,0>Rm/4N/3@Rt,1P19t2'6PmP4f=RtO4b4W3W1P4P1O2n2001000010121000000b7b8b;b<b>b?PRPTP<PWPXPYPLPZP[PSP=PUP0P\P]1NPPR\/4a,5`PbPhPgPiPjP3Prg00H`RrAP3;;=J3sC>,7kP7PEb5b9b:X03141NR;13;@R;,4\'5^03P1PmO1b4X3eX1dP4P1O2n2001000000121000000b7b8b;b<b>b?EO1<OP,5QP314INRQ/3@RO131N/<@f5,0>'5X=3P3PI13ONRO/<@POP@%a:R:PIP[PSP=PUP0f6RI,0>RO#211O@10>bRb#211b@'611@b19b2'6'APKf8,0>RK#2RbPhPgPiPjPkPoPpPkPBPp1Cql,7k=Mko=Sk6C@C@P7PEb5b9b:X03X6f%28118@'6/A9\C\5^03^6fP111@c19c2'6PcP4P^O4b4X3]W1P4P1O2n2001000000121000000b7b8PXPYPLPZP[PSP=PUP0Pb11K@14VN/3@/3N1N@:RK/4V'5PI%2_11c@PhPgPiPjP3AD3sAPr1B3:9P3n=J3lC>,7kP7PEb5b9b:X0313;N14K1'5^03P110>tO1b4W3W1P4P1O2n2001000000121000000b7b8b;b<EOC`1<QPP1Ebb115MFePJ%cGEI10>H1d>GEIO4b114D2%eDEI1]82=8?8ebCWDWEo"). Qed.

Lemma edenot_addw0_errno : forall E a,
  (2 ^ 64 - 4095 <= bv_unsigned (edenot E a))%Z ->
  edenot E (EAluw ALU_ADD a (ELit 0)) = edenot E a.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_3"] "h01bh11Eh22Hah31ap;1p;2p;3p;6g002Yj10Tg003\j13Tg004:j2@Tg017fj17Tg00O1j2GTg003>j14Tg00`4j22Tg001Kj2>Tg007Gj2=Tg000Nj19Tg01Qhj3<Tg01f\j35Tg01gGj18Tg01goj3;Tg0011j36Tg01Adj2FTg01dmj2ETg01hWj2DTg01ijj2ATg00BRj6:Tg0057j2BTg01k5j1?Tg01lCj3CTf0R0#7#7p=1g00c[g00dhg00E6R1#0R2#3%02#0#0#0R2#0R3#3'@%71R1#1#1#1#1#1#3'G%43R3f1R4/20'>'=%42R2#9R5%01#0#4R1g00E[R6g01T75<1R7752R8%93R9g00f6R:f3f2R;'2R<#8;;09523;6<X05P912;4R51F17'EA690<X091D50%85=;:895231A57E:1B36#8g01mQE:%?69C:4,2;=695eW2W3W1o"). Qed.

(* [comment removed for export] *)
Lemma rdn_byte_Z : forall segs m a n bs j,
  rdn segs m (Z_to_bv 64 a) n = Some bs -> (j < n)%nat -> (0 <= a)%Z -> (a + Z.of_nat j < 2 ^ 64)%Z ->
  rdn segs m (Z_to_bv 64 (a + Z.of_nat j)) 1%nat = Some [nth j bs (Z_to_bv 8 0)].
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_3"] "h02Hah11Rh24__x1h34__x2h41Hh52Hjh63Hj0h72Hnh87__arithh94__ffh:6__sat1h;6__sat2h<8__varmaph=5__with>1ah?1bh@2bshA4cstrhB5cstr0hC1jhD1mhE1nhF4segshG1zp;1p;2p;4p;3p;8p;6p;7p;<g008gj1>Tg002Yj14Tg003>j1GTg000Nj1CTg01EPj1LTg0057j21Tg01F2j45Tg01G9j29Tg0011j33Tg01VmR0j2DTg01G[R1j12Tg00KDj27Tg003\j1OTg004:j2jTg006kR2j26Tg01nfj8aTg01K]j1MTg01LXj3KTg01H`j1?Tg01[[j4:Tg008Gj1HTg01K=j38Tg001Kj2FTg01M=j2ZTg00MLj6ETg00>Ij2=Tg0200j4XTg01H;j1JTg006Cj2WTg007cj3VTg01I?j2ATg01Ihj3BTg01JQj2UTg015dj2TTg009Gj1QTg016Bj4PTg009ej1RTg00:Cj1STg00:nj2NTg016`j2ITg00<4j4<Tg018hj1iTg017Cj3hTg00;Qj3gTg019Jj7fTg00=gj2`Tg00>cj2_Tg00?Oj3^Tg00?nj4]Tg00D[j2bTg019nj2cTg007Gj2\Tg020Wl<dTg00<_j7eTg01=^j8[Tg00E[R3f0R4'\p=0g012hR5g00C_R6P0P1P2g021<f5R2f4R1f3R0f2R7f1R8P4M<dp=YP8g00GAR9g00G`R:P:g00H@R;P4g00IGFep=;P0P9P:P:P;P7P8P4G[p=@g01O^#>g00E6R<#4R=#4#4R>#4#4#4R?#GR@#CRA%G>R>#CRB#L[%>BRC%LCRDP2P111@0P7C519C8331D80%02f6RE%20'7%O=RF%O?R?'jRG'6f9RHf8RIPEf7RJ,1@RKP2P1P0P7GaPHPI%M19K@Kg01P]RK#?RLC5PBP1P211>3R>C:%HBRM58B,9C53DPA11@IRN%M25K@f;ROf:RPP4PLC5PBPEPJP>C:=8BM,9CRQ53DX?AP41F@N%22'7,1@RA1ZN2EEPPPHPAPLC5PBP2PEP>C:=8BM,9C53DP611@H,F@f<R2PO%2JRA,74,1@PLC5PBPJPIP>C:=8BM,9C53DXG6P4PH1DEI%2ERC%2IRM'6RBPEPC1=6CPIPM1=6MEYP1CXPB%JJ%0A%JP%2P#01WF?163F%0?163G[[%0FRAg00F9RJAVF?8UW0%0G\J^0Ag00FURA%?LRJ#?,A61A6J1A6K5B65B6g01Q<'U%HA38%>AP61T67P8%Q6CP%R6%S6RAP61N63RKg01>iRJ1I6=R=C<,;A%i:R?PAP61I6<R<=h6=g01>BR=1N6F=g6@RFC<,;AP?PAP6PKPJP<C<,;ARJP?PAP9P:P:P;PJP6P<P=PFC<,;AFfC@C@C@1`A;P4P7g00IgRAg00JGR;'=1_47=3A;dA^638C]b9b<b=X26X36%081787/6G%07%00160G'b[[[^26^36P4%22f?P1PIPHO5b8b:b;bBbAb6,cHEEPOPP17HC,1@PLC5=3DQP4b1b1b1W7W0W5W4XC5W@XE5X>6WDWFo"). Qed.

Lemma nth_app_l : forall {A} (l l' : list A) (d : A) j, (j < length l)%nat -> nth j (l ++ l') d = nth j l d.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_3"] "h01Ah11dh21jh31lh42l'p;1p;2p;6p200R0p101[[p4p710p8P0g01]cR1p4p710p8P0p101]Fp4p710p8P0g021^R2p4p710p8g008gj10TP1j23Tg01Vmj22TP2j61Tf0R2#0f1R1#0f2R3g012hf4R4f3R5'3,22f5P4P5P3P1P2E1UW2W1W4W3X00o"). Qed.

Lemma In_nth_neq : forall {A} (l : list A) (x d : A) j, ~ In x l -> (j < length l)%nat -> nth j l d <> x.
Proof.
ltac2:(KReplay.run1 (kr_t_LibTail ()) ["FPX_3"] "h01xh11Ah21Eh32Hjh42Hnh51dh61jh71lp;1p;3p;2p;4p;5p;6p200R0g01RKR1p4p710p8P0g00MLR2p4p710p8P0g01[[R3p4p710p8P0g01]cR4p4p710p8P0g022;R5p4p710p8g008gj18TP1j32Tg01SAj11TP4j23Tg01Vmj27TP3j40Tg0011j36TP5j54TP2j65Tf0R2#8f1R5f2R3g012hf4R4f3R1723#1f5R6/34,75f6R7P7P3P6P1C0;64R8P3f7R3P3P1P7P4C0f8?223X03P3P1P7P4P5D4P6P2E5O1W2%18eW3W4W6W5W0W7X10o"). Qed.
End FPX_3.



Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
