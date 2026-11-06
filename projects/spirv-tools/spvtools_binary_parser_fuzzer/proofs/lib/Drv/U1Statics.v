(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec SeqExec StoreOk MemSplit LibIface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib StaticsGen U1CxxTable.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1Statics () := "C47Corelib7Classes?RelationClasses9ReflexiveC59OSSVerify5KrLib3Drv7Overlay3runC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib3Drv7RunsLib8runs_subC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib3Drv9U1Statics4D_SXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv9U1Statics4D_RDC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Drv7RunsLib4pinsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLib8pins_subC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib3Drv9U1Statics8D_SX_subC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02c59OSSVerify5KrLib3Drv9U1Statics;runs_withinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLib7in_runsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLib?in_runs_coveredC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C49OSSVerify5KrLib8LibIface5ly_rwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface9in_rangesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leI47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2or01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01c69OSSVerify5KrLib3Drv9U1Statics2Ly1LC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv9U1Statics;D_SX_withinC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib3Drv9U1Statics;D_RD_withinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7Overlay;lookup_byteC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib3Drv7RunsLib?runs_sub_lookupC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib3Drv7Overlay;lookup_runsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv9U1Statics<AT_SLOT_ADDRC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib5Lists7ListDef3mapC49OSSVerify5KrLib8LibIface>ly_new_handlerC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface4zwinC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C49OSSVerify5KrLib8LibIface8ly_relroC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalI47Corelib4Init5Logic2or00C47Corelib7Classes?RelationClasses;reflexivityC47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses=iff_Reflexive".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Module Ly := U1Layout.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition TD_LOCALE : Z := 0x1023e8.

Definition AT_SLOT_ADDR : Z := 0x122468.

Definition D_RD : list run := D_CXX.

Definition D_SX : list run := Eval vm_compute in RunsLib.drop_run AT_SLOT_ADDR D_RD.

Lemma D_SX_sub : runs_sub D_SX D_RD = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1Statics ()) [] "p;2p;3p-1p10000p4p710p9p1000\p4p70p1001Pp4p710p8g001lj22Tg002Fj21Tg003?j30Tg003YR0g0049R1'2g004Yg005P'1=001do"). Qed.

Lemma pins_D_SX : forall M, pins D_RD M -> pins D_SX M.
Proof.
ltac2:(KReplay.run1 (kr_t_U1Statics ()) [] "h01Hh11Mp;1p;2p;5g006Gj10Tg006lj12Tg007Jj11Tg007mj13Tg008Oj25Tg009Dj54Tg00:=#0#0#0R0#0#0#0#2#1%20#1#3[g005PR0f0R1'5g004YP0f1g00:bP1D4W0W1o"). Qed.

Definition runs_within (rs : list run) (lo hi : Z) : bool :=
  forallb (fun r : run => (lo <=? fst r) && (fst r + Z.of_nat (length (snd r)) <=? hi)) rs.

Lemma D_SX_within : runs_within D_SX 0xef000 0x124000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1Statics ()) [] "p;2p;1p;3g001lj27Tg00;]j10Tg006Gj11Tg00<Bj14Tg00<`j36Tg003?j35Tf0R0#1#1#1#1p=2%10#1p=3g003YR0g0049R1'7g004Yg00:=R2#0#0#1#0#0#0#0#2#2#2#4%32#0#3#0#3#2#2#2#436=501do"). Qed.

Lemma D_SX_rw : forall a, in_runs D_SX a -> in_ranges (ly_rw Ly.L) a.
Proof.
ltac2:(KReplay.run1 (kr_t_U1Statics ()) [] "p'0h01rh11Hh22H1h32H2h42Hah52Hbh64__x1h74__x2h84__x3h92hih:1mh;1nh<3Hinh=2Hrh>7__arithh?4__ffh@8__varmaphA5__withB1ahC4cstrhD2lohE1xi001xp;2p;3p;1p;6p;4p;7p;8g00=^j2tTg00>Vj3sTg00?Vj1JTg00@6j24Tg00@SR0j26Tg00@nR1j2NTg00AHj1[Tg00B;j2FTg00;]j19Tg006Gj18Tg00<Bj1TTg00C2j22Tg00COj2jTg00Cmj3eTg00DIj3bTg00Dlj6aTg00EGj3^Tg00Ejj25Tg00FFj2]Tg00Ffj2\Tg00GFj3<Tg003?j3MTg00G]j1LTg001lj2KTg00H=j3ZTg00HWj1XTg00I<j1ITg00I\j1?Tg00J;j2=Tg00Jdj3@Tg00KMj2HTg00L9j3WTg00LYj2VTg00M7j4rTg00MUj1qTg00N3j1pTg00N^j2BTg00OAj3oTg00Odj2PTg00PGj1lTg00Pij4ETg00QTj2kTg00R6j2iTg00Rbj3hTg00SAj4gTg00T3j4fTg00TNj4QTg00Thj3cTg00UEj3RTg00Ubj2UTg00VBj2OTg00V^j4mTg00W>j7nTg00Wbj7`Tg00XFj8_Tg000\R2f0R3g004YR43<p=Gg00XjR5f1R6;c3p=1AR563,U5#Ip=7f3R7f2R8'51O63'6p=3%83#8#8#8p=:%83#8p=Dg003YR9g0049R:7M3p=0P5P5P6P3Cmp=AAR563,U5p=YP5P6g00YHP3CEp=>P6g00YoR;g00ZNR<P<g00ZnR=P3g00[NFnp=;P8P;P<P<P=P6P3F`p=SP7P;P<P<P=P8P6P3G_p=C1O63,68p=d1t43As463%G3R;%J5R>/13R?P8P817>3,4?R@C3'6X02,N2P1P2P?P7P7P@C3,6;X02g00[n#[R1/F7P3P?f5RAPAP@C3,6;P0%G611>6RBf6RCPC17>6,4BC3f7RB,F1P3%G7f4RD,1>REf9RFPF17>D,4EC3g00:=RE#9RG#9#8#9#9#9#9#:#:#:#TRH/2?%DE#9#D#9#D#:#:#:#TR?,2@'jX02R@=e24#0RIP@P6O1#0\;^E2R;[PI\;Ab2@4g00\ePAP6EaP@PAO1#011>CRA,2HR@17>C,4A/2?RA;^3%0@%0A'6P011>BRA,2H#017>B,4A/2?#0f=,F1P311>F,2H#0f:RF,1>17>F'4/2?#0P01263#01586[R015631286#0RF[1578RA\F1]63P6n2001000000120000000X:5X;5RFP0^:5^;5R0P3PHf<RB,1>R@P8O315H@PFP0P3f>R0,1>17>0'4R0P?P7O3150?P51\55R01A63;<1P6fFRFPFP3C3'6X95,N5XD5PHP51AH3=<01PHfER@P@P3C3'6X95P?1AH?R@=<01PHfDR1P1P?C3AM0@@%L09<0@1K0@3Zf?,Y>R@#Xg00]cR0%I@'5g00^AR@g00^mR1#?RC#?R4#?R;#?,=51=5C1=51R15@55@5g00_LRC'H1=5;1=54=@515@5/HC%L@5W@3W%J@P51V58P61V57Cr%q5%p5R@%8E,B5RC1B5G5o5RG1P5?R1'>,;@%l<R<P@1P5HR4/>C,;@P<P@1B5ERE,>C,;@P5PEg00`8RCPGCE,;@5S@P<1>4E,;@P5PEPCP1CE,;@5S@CCCCCC1k@=P3P81K9:1i38#0dAh506Cgb?b@bAX65X75X851468/5?15H8147D9dA8PHP7P7P?C3[[[^65^75^85P3fAR?,7>11>?PFP8PDPBO6b>bCCfCQCQb3b1b2b1W3W2P6P3O2n2001000000121000000b5b5W=W<P6P3O2n2001000000121000000W1X02P6P3O2n2001000000121100000b4W4XB5o"). Qed.

Lemma D_RD_within : runs_within D_RD 0xef000 0x124000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1Statics ()) [] "p;2p;1p;3g001lj27Tg00;]j10Tg006Gj11Tg00<Bj14Tg00<`j36Tg003?j35Tf0R0#1#1#1#1p=2%10#1p=3g003YR0g0049R1'7g005Pg00:=R2#0#0#1#0#0#0#0#2#2#2#4%32#0#3#0#3#2#2#2#436=501do"). Qed.

Lemma D_RD_rw : forall a, in_runs D_RD a -> in_ranges (ly_rw Ly.L) a.
Proof.
ltac2:(KReplay.run1 (kr_t_U1Statics ()) [] "p'0h01rh11Hh22H1h32H2h42Hah52Hbh64__x1h74__x2h84__x3h92hih:1mh;1nh<3Hinh=2Hrh>7__arithh?4__ffh@8__varmaphA5__withB1ahC4cstrhD2lohE1xi001xp;2p;3p;1p;6p;4p;7p;8g00=^j2tTg00>Vj3sTg00?Vj1JTg00@6j24Tg00@SR0j26Tg00@nR1j2NTg00AHj1[Tg00B;j2FTg00;]j19Tg006Gj18Tg00<Bj1TTg00C2j22Tg00COj2jTg00Cmj3eTg00DIj3bTg00Dlj6aTg00EGj3^Tg00Ejj25Tg00FFj2]Tg00Ffj2\Tg00GFj3<Tg003?j3MTg00G]j1LTg001lj2KTg00H=j3ZTg00HWj1XTg00I<j1ITg00I\j1?Tg00J;j2=Tg00Jdj3@Tg00KMj2HTg00L9j3WTg00LYj2VTg00M7j4rTg00MUj1qTg00N3j1pTg00N^j2BTg00OAj3oTg00Odj2PTg00PGj1lTg00Pij4ETg00QTj2kTg00R6j2iTg00Rbj3hTg00SAj4gTg00T3j4fTg00TNj4QTg00Thj3cTg00UEj3RTg00Ubj2UTg00VBj2OTg00V^j4mTg00W>j7nTg00Wbj7`Tg00XFj8_Tg000\R2f0R3g005PR43<p=Gg00XjR5f1R6;c3p=1AR563,U5#Ip=7f3R7f2R8'51O63'6p=3%83#8#8#8p=:%83#8p=Dg003YR9g0049R:7M3p=0P5P5P6P3Cmp=AAR563,U5p=YP5P6g00YHP3CEp=>P6g00YoR;g00ZNR<P<g00ZnR=P3g00[NFnp=;P8P;P<P<P=P6P3F`p=SP7P;P<P<P=P8P6P3G_p=C1O63,68p=d1t43As463%G3R;%J5R>/13R?P8P817>3,4?R@C3'6X02,N2P1P2P?P7P7P@C3,6;X02g00[n#[R1/F7P3P?f5RAPAP@C3,6;P0%G611>6RBf6RCPC17>6,4BC3f7RB,F1P3%G7f4RD,1>REf9RFPF17>D,4EC3g00:=RE#9RG#9#8#9#9#9#9#:#:#:#TRH/2?%DE#9#D#9#D#:#:#:#TR?,2@'jX02R@=e24#0RIP@P6O1#0\;^E2R;[PI\;Ab2@4g00`_PAP6EaP@PAO1#011>CRA,2HR@17>C,4A/2?RA;^3%0@%0A'6P011>BRA,2H#017>B,4A/2?#0f=,F1P311>F,2H#0f:RF,1>17>F'4/2?#0P01263#01586[R015631286#0RF[1578RA\F1]63P6n2001000000120000000X:5X;5RFP0^:5^;5R0P3PHf<RB,1>R@P8O315H@PFP0P3f>R0,1>17>0'4R0P?P7O3150?P51\55R01A63;<1P6fFRFPFP3C3'6X95,N5XD5PHP51AH3=<01PHfER@P@P3C3'6X95P?1AH?R@=<01PHfDR1P1P?C3AM0@@%L09<0@1K0@3Zf?,Y>R@#Xg00]cR0%I@'5g00^AR@g00^mR1#?RC#?R4#?R;#?,=51=5C1=51R15@55@5g00_LRC'H1=5;1=54=@515@5/HC%L@5W@3W%J@P51V58P61V57Cr%q5%p5R@%8E,B5RC1B5G5o5RG1P5?R1'>,;@%l<R<P@1P5HR4/>C,;@P<P@1B5ERE,>C,;@P5PEg00`8RCPGCE,;@5S@P<1>4E,;@P5PEPCP1CE,;@5S@CCCCCC1k@=P3P81K9:1i38#0dAh506Cgb?b@bAX65X75X851468/5?15H8147D9dA8PHP7P7P?C3[[[^65^75^85P3fAR?,7>11>?PFP8PDPBO6b>bCCfCQCQb3b1b2b1W3W2P6P3O2n2001000000121000000b5b5W=W<P6P3O2n2001000000121000000W1X02P6P3O2n2001000000121100000b4W4XB5o"). Qed.

Lemma in_runs_D_SX_RD : forall a, in_runs D_SX a -> in_runs D_RD a.
Proof.
ltac2:(KReplay.run1 (kr_t_U1Statics ()) [] "p'0h01Eh12Hah21oi001oh31Hh42H0h51ah61bh71ei011zp;2p;1p;3p;6g00=^j26Tg00a]j21Tg007mR0j1:Tg001lj25Tg003?j30Tg00PGj1;Tg00bYj12Tg00c2j23Tg00cTj69Tg00d0j24Tg00dOj67Tg00eOj68Tg00XjR1g004YR2f0R3'6f1R4,12%:1R51553f2R6,12=053P0P1f4,12=053%;1R79054#2g005PR8f6'1=057#2]1]0P4f5R9,1213135051314=057#2P51316R:A0537#2X25A05:7R:P5f3R;,31P0P1p-0P3g00emg00fIR0n10110000021000000X75g00ffP7P3E9P01403b4W3%2:ef7R:,18P2P8P:P6g00:bP4E7E8W1W0X61P3O1112;=057A0577#21189=057#2P31557O1'4W1W0n10110000021010100P3P6O2b0b21684eW1W5o"). Qed.

Lemma D_RD_slot : lookup_runs D_RD AT_SLOT_ADDR 4 = Some [1; 0; 0; 0].
Proof.
ltac2:(KReplay.run1 (kr_t_U1Statics ()) [] "p;1p;3p;2g00?Vj1:Tg007mj19Tg00<Bj14Tg00G]j13Tg00L9j32Tg00c2j28Tg001lj25Tg00I\j10Tg00gBj36Tg003?j37Tg00XjR0g00]cf032p=1%:0R1#9R2g00:=#4%30#1#1#1520,81R1'5g005Pg00h>g00^m#0#0#0#036=721do"). Qed.
Lemma D_RD_head : lookup_runs D_RD 0x122470 8 = Some (map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 0x122478))).
Proof.
vm_compute. reflexivity. Qed.

Lemma handler_rw : forall a, zwin (ly_new_handler Ly.L) (ly_new_handler Ly.L + 8) a -> in_ranges (ly_rw Ly.L) a.
Proof.
ltac2:(KReplay.run1 (kr_t_U1Statics ()) [] "h04__x1h12hih22Hah37__arithh44__ffh58__varmaph65__with71ah82lop;1p;2p;3p;4p;8p;7g00l1j1XTg006Gj11Tg00<Bj1:Tg00@6j2BTg00lmj3UTg00Ffj2STg00AHj1ITg00GFj38Tg00Ejj2;Tg00VBj29Tg00@Sj24Tg00@nj2WTg00;]j10Tg003?j3@Tg00G]j1?Tg001lj2>Tg00H=j3RTg00?Vj1QTg00LYj2NTg00MUj1KTg00N3j1JTg00Odj25Tg00N^j2HTg00Pij46Tg00OAj3GTg00PGj1LTg00XFj8FTg00QTj2ETg00R6j2MTg00Rbj3DTg00SAj4OTg00T3j4PTg00TNj4=Tg00V^j4CTg00W>j7TTg00Wbj7VTf0R0#1#1p=3g00XjR1P1f1R2P0CCp=<%10#1#1#1p=2P2g00YoR3g00ZNR4P4g00ZnR5P0g00[NFTp=7f2R6P3P4P4P5P2P0FVp=Ag00[nR7#XR8g00:=R9#1#3#:R:,B8;U0P11S11R81<20%I7R738f3R;,;219;0'4'4X11,W1X81%09#0#1#0#0#0#0#2#2#2#:R;P11<;0=8871;;61960'4'4X11%39#0#3#0#3#2#2#2#:R<1<;<R==8871;;2192<'4R7A@8==%?8988=1>8=3Rg00^AR=#?%Q=1N12%K1%J1R=P3P4P4P5P1%39#2#2#0#1#0#1#3#2#:R3,51R8g00YHR>1H19R9C6,7=P1P9g00`8R?151:9G18C6,7=5A=%L4P1151;P>P9C6,7=P1P9P?151<C6,7=5A=GF1E=5P0P6g003YR=g0049R5'>1M06=@=5dg00]c=D12COb4b5b6X011;301B3:,90'4P7[^01P0P6P2O2b3CPC=C=W2X71o"). Qed.

Lemma handler_range : 0 <= ly_new_handler Ly.L /\ ly_new_handler Ly.L + 8 <= 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_U1Statics ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__witp;1p;2p;3p;4p;7g006Gj12Tg00<Bj13Tg00m_j2>Tg00VBj2:Tg00Ejj21Tg00nGj2LTg00ndj3BTg00G]j1@Tg00?Vj1?Tg00oHj1=Tg00MUj1<Tg00N3j1;Tg00Odj24Tg00;]j19Tg00Pij45Tg00OAj3NTg006lj1MTg00ofj3KTg00Wbj7HTg00QTj2GTg001lj2ATg00R6j2CTg003?j3DTg00Rbj3ETg00SAj4FTg00@6j28Tg00@Sj26Tg00l1j1ITg00W>j7JTf0R0#2#2p=0f1R1g00YoR2g00ZNR3P3g00ZnR4P0g00[NFJp=7g00:=R5#2R6#3R7%06R6#2#0R8#3R9'>g00]cR:/:711:91L79R;,::[[11:7R<g00emR=AB791UW011:;\=^0<g00^AR<#@%?<g00XjR<#=%<<%;<R=P2P3P3P4P<14<:g00YHR3%05#0#0#0#0#9#2#9#2#0#0#0#3R5,4<R2C5,7=P<%36R6,4<9N<2P314<7%M85K<C5,7=FH1G=4P0f2R=g003YR4g0049R8'A1C0==D48dAE<:1CFb2b5b611:51856/1;'6P0b1b3b4g00[n#IR0,1:1806/1;'6eo"). Qed.

Lemma relro_range : forall a, in_ranges (ly_relro Ly.L) a -> 0 <= a < 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_U1Statics ()) [] "p'0h01Hh12Hrh22hih32loh42Hah53Hinh64__x1h71eh87__arithh94__ffh:6__sat0h;6__sat1h<8__varmaph=5__with>1ai001pi011xi021zp;1p;2p;3p;6p;4p;8p;7g010Ij1\Tg00B;j2[Tg00FfR0j2MTg00GFj38Tg00@SR1j26Tg00@nR2j2ATg006Gj11Tg00<Bj19Tg00nGj2ETg00;]j17Tg003?j34Tg011?j6BTg00m_j2VTg00VBj2=Tg00ndj3UTg00G]j1TTg00?Vj1LTg00LYj2KTg00MUj1JTg00N3j1ITg00Odj2;Tg00N^j2HTg00Pij4<Tg00PGj1GTg006lj1FTg00ofj3NTg00XFj8OTg00QTj2PTg001lj2QTg00R6j2DTg00Rbj3RTg00SAj4STg00cTj7CTg00V^j4ZTg00Ejj2?Tg00W>j7XTg00Wbj7WTg00XjR3P3f1R4f0R5CZp=2f3R6f2R7'?1=45'6p=0%15#1#1#1p=5g00]cR8/?71=45'6p=3%15#1p=Y1?85p=>P4g00YoR9g00ZNR:P:g00ZnR;P5g00[NFXp=:P7P9P:P:P;P4P5FWp=@g00[n#\R</[5P2P31M33R=1245;8<R>P4P6P6P5C0'6X23,A3X33g00:=R?#1R@#9RA%1@#5R@#9RB'ERC9377P5P4f5RDPDP5C0,6>X23,A3P2P31275=8=<P7f6R2P2P5C0'6X23A322CP5f4R>/25=8=<P>f8REPEP5C0'6P112D4=8=<PDf9R1P1P4C0f:RF?3FCP5f7RG/26=8=<PEf<R<P<P>C0g011\%7?#7#1#7R>#1#Y#5#5#5#9RH%7>#7#7#5#5#5#9R>'2RI121D54=g00fIR1f>RJ?3JCP412F294=IP=P3P0P3P3P3P5P5n2001100000120102102X7=PIf;R2/2GP5EBA43>GP=P3P0P3P3P3P5P4n2001100000120102102X7=PI12<EP4EBA43H<f=943HP3PHP5fCREPEP2C0A43><fERE?3EC[]1X33PHfBRIPIPFC0A43>2P3P>PHPEPEP5C0fFRE?3EC]1X23PHfDREPEP>C01VAB1=8A%>B1=8C[[%>AREg00emR2AUAB4UW4%>C\2^4Eg00^ARE#T%LE1K34%J3%I3REP9P:P:P;P31;3Hg00YHR91H3?R?C<,:EP3P?g00`8R21;3>C<,:E5@E%G:P31;38P9P?C<,:EP3P?P21;3A%F@5N3C<,:E5@EGO1PE;P5P7g003YREg0049R;'Q1D57=4E;dAR384CSb9b<b=X63PHP5P5P>C0A344C[^63P5fHP6O2b8b:b;W1P<P5P4FCW0W1PJP5PDFCW0P5O1b0P5O1b0W5P5O1P1f@RD?3DCP5n010000000X01P5O1n200100000021100010000W1W5P4P5O2n2001000000121000000W0X23P4P5O2n2001000000121101000W0X33P4P5O2n2001000000121101000W0X>3o"). Qed.

Definition U1ST : StaticsIface Ly.SEGS Ly.L :=
  drv_statics Ly.SEGS Ly.L D_SX D_SX_rw handler_rw handler_range relro_range.

Lemma u1_region : forall a,
  sx_region U1ST a <-> (in_runs D_SX a \/ zwin (ly_new_handler Ly.L) (ly_new_handler Ly.L + 8) a).
Proof.
ltac2:(KReplay.run1 (kr_t_U1Statics ()) [] "h01ap;2p;1p;3p;4g00=^j27Tg00l1j16Tg006Gj10Tg00<Bj11Tg00@6j25Tg00lmj34Tg011\j23Tg0126j42Tg00Xjp-0g012dg013=g004Yf0R0'7g00[n#6R1g00:=#0#0#0#1,51;40'3C2W0o"). Qed.

