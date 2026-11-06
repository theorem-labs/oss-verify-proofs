(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec SeqExec StoreOk MemSplit LibIface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib StaticsGen S1CxxTable.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1Statics () := "C47Corelib7Classes?RelationClasses9ReflexiveC59OSSVerify5KrLib3Drv7Overlay3runC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib3Drv7RunsLib8runs_subC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib3Drv9S1Statics4D_SXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv9S1Statics4D_RDC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Drv7RunsLib4pinsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLib8pins_subC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib3Drv9S1Statics8D_SX_subC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02c59OSSVerify5KrLib3Drv9S1Statics;runs_withinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLib7in_runsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLib?in_runs_coveredC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C49OSSVerify5KrLib8LibIface5ly_rwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface9in_rangesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leI47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2or01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01c69OSSVerify5KrLib3Drv9S1Statics2Ly1LC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv9S1Statics;D_SX_withinC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib3Drv9S1Statics;D_RD_withinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7Overlay;lookup_byteC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib3Drv7RunsLib?runs_sub_lookupC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib3Drv7Overlay;lookup_runsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv9S1Statics<AT_SLOT_ADDRC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib5Lists7ListDef3mapC49OSSVerify5KrLib8LibIface>ly_new_handlerC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface4zwinC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C49OSSVerify5KrLib8LibIface8ly_relroC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalI47Corelib4Init5Logic2or00C47Corelib7Classes?RelationClasses;reflexivityC47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses=iff_Reflexive".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Module Ly := S1Layout.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition TD_LOCALE : Z := 0x100688.

Definition AT_SLOT_ADDR : Z := 0x120708.

Definition D_RD : list run := D_CXX.

Definition D_SX : list run := Eval vm_compute in RunsLib.drop_run AT_SLOT_ADDR D_RD.

Lemma D_SX_sub : runs_sub D_SX D_RD = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1Statics ()) [] "p;2p;3p-1p10000p4p710p9p1000\p4p70p1001Pp4p710p8g001lj22Tg002Fj21Tg003?j30Tg003YR0g0049R1'2g004Yg005P'1=001do"). Qed.

Lemma pins_D_SX : forall M, pins D_RD M -> pins D_SX M.
Proof.
ltac2:(KReplay.run1 (kr_t_S1Statics ()) [] "h01Hh11Mp;1p;2p;5g006Gj10Tg006lj12Tg007Jj11Tg007mj13Tg008Oj25Tg009Dj54Tg00:=#0#0#0R0#0#0#0#2#1%20#1#3[g005PR0f0R1'5g004YP0f1g00:bP1D4W0W1o"). Qed.

Definition runs_within (rs : list run) (lo hi : Z) : bool :=
  forallb (fun r : run => (lo <=? fst r) && (fst r + Z.of_nat (length (snd r)) <=? hi)) rs.

Lemma D_SX_within : runs_within D_SX 0xee000 0x122000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1Statics ()) [] "p;2p;1p;3g001lj27Tg00;]j11Tg006Gj10Tg00<Bj14Tg00<`j36Tg003?j35Tf0R0#0#0#0#0p=2%00#0p=3g003YR0g0049R1'7g004Yg00:=R2#1#1#0#1#1#1#0#2#2#2#4%32#1#0#3#1#0#2#2#2#436=501do"). Qed.

Lemma D_SX_rw : forall a, in_runs D_SX a -> in_ranges (ly_rw Ly.L) a.
Proof.
ltac2:(KReplay.run1 (kr_t_S1Statics ()) [] "p'0h01rh11Hh22H1h32H2h42Hah52Hbh64__x1h74__x2h84__x3h92hih:1mh;1nh<3Hinh=2Hrh>7__arithh?4__ffh@8__varmaphA5__withB1ahC4cstrhD2lohE1xi001xp;2p;3p;1p;6p;4p;7p;8g00=^j2tTg00>Vj3sTg00?Vj1ITg00@6j24Tg00@SR0j28Tg00@nR1j2MTg00AHj1[Tg00B;j2CTg00;]j19Tg006Gj11Tg00<Bj1TTg00C2j23Tg00COj2jTg00Cmj3eTg00DIj3bTg00Dlj6aTg00EGj3^Tg00Ejj25Tg00FFj2]Tg00Ffj2\Tg00GFj3<Tg003?j3LTg00G]j1KTg001lj2JTg00H=j3ZTg00HWj1XTg00I<j1HTg00I\j1?Tg00J;j2=Tg00Jdj3@Tg00KMj2GTg00L9j3WTg00LYj2VTg00M7j4rTg00MUj1qTg00N3j1pTg00N^j2BTg00OAj3oTg00Odj2OTg00PGj1lTg00Pij4ETg00QTj2kTg00R6j2iTg00Rbj3hTg00SAj4gTg00T3j4fTg00TNj4QTg00Thj3cTg00UEj3RTg00Ubj2UTg00VBj2NTg00V^j4mTg00W>j7nTg00Wbj7`Tg00XFj8_Tg000\R2f0R3g004YR43<p=Fg00XjR5f1R6;c3p=2AR563,U5#Hp=7f3R7f2R8'51N63'8p=6%13#1#1#1p=:%13#1p=Pg003YR9g0049R:7L3p=0P5P5P6P3Cmp=AAR563,U5p=YP5P6g00YHP3CEp=>P6g00YoR;g00ZNR<P<g00ZnR=P3g00[NFnp=;P8P;P<P<P=P6P3F`p=SP7P;P<P<P=P8P6P3G_p=D1N63,88p=d1t43As463%F3R;%I5R>/23R?P8P817>3,4?R@C6'8X02,M2P1P2P?P7P7P@C6,8;X02g00[n#[R1/C7P3P?f5RAPAP@C6,8;P0%F612>6RBf6RCPC17>6,4BC6f7RB,C1P3%F7f4RD,2>REf9RFPF17>D,4EC6g00:=RE#9RG#9#1#9#9#9#1#:#:#:#TRH/3?%PE#9#1#P#9#1#:#:#:#TR?,3@'jX02R@=e24#0RIP@P6O1#0\;^E2R;[PI\;Ab2@4g00\ePAP6EaP@PAO1#012>CRA,3HR@17>C,4A/3?RA;^3%0@%0A'8P012>BRA,3H#017>B,4A/3?#0f=,C1P312>F,3H#0f:RF,2>17>F'4/3?#0P01363#01586[R015631386#0RF[1578RA\F1]63P6n2001000000120000000X:5X;5RFP0^:5^;5R0P3PHf<RB,2>R@P8O315H@PFP0P3f>R0,2>17>0'4R0P?P7O3150?P51\55R01A63;<1P6fFRFPFP3C6'8X95,M5XD5PHP51AH3=<01PHfER@P@P3C6'8X95P?1AH?R@=<01PHfDR1P1P?C6AL0@@%K09<0@1J0@3Zf?,Y>R@#Xg00]cR0%H@'5g00^AR@g00^mR1#?RC#?R4#?R;#?,=51=5C1=51R15@55@5g00_LRC'G1=5;1=54=@515@5/GC%K@5W@3W%I@P51V58P61V57Cr%q5%p5R@%1E,B5RC1B5G5o5RG1O5?R1'>,;@%l<R<P@1O5HR4/>C,;@P<P@1B5ERE,>C,;@P5PEg00`8RCPGCE,;@5S@P<1>4E,;@P5PEPCP1CE,;@5S@CDCDCD1k@=P3P81J9:1i38#0dAh506Cgb?b@bAX65X75X851468/5?15H8147D9dA8PHP7P7P?C6[[[^65^75^85P3fAR?,7>12>?PFP8PDPBO6b>bCCfCQCQb3b1b2b1W3W2P6P3O2n2001000000121000000b5b5W=W<P6P3O2n2001000000121000000W1X02P6P3O2n2001000000121100000b4W4XB5o"). Qed.

Lemma D_RD_within : runs_within D_RD 0xee000 0x122000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1Statics ()) [] "p;2p;1p;3g001lj27Tg00;]j11Tg006Gj10Tg00<Bj14Tg00<`j36Tg003?j35Tf0R0#0#0#0#0p=2%00#0p=3g003YR0g0049R1'7g005Pg00:=R2#1#1#0#1#1#1#0#2#2#2#4%32#1#0#3#1#0#2#2#2#436=501do"). Qed.

Lemma D_RD_rw : forall a, in_runs D_RD a -> in_ranges (ly_rw Ly.L) a.
Proof.
ltac2:(KReplay.run1 (kr_t_S1Statics ()) [] "p'0h01rh11Hh22H1h32H2h42Hah52Hbh64__x1h74__x2h84__x3h92hih:1mh;1nh<3Hinh=2Hrh>7__arithh?4__ffh@8__varmaphA5__withB1ahC4cstrhD2lohE1xi001xp;2p;3p;1p;6p;4p;7p;8g00=^j2tTg00>Vj3sTg00?Vj1ITg00@6j24Tg00@SR0j28Tg00@nR1j2MTg00AHj1[Tg00B;j2CTg00;]j19Tg006Gj11Tg00<Bj1TTg00C2j23Tg00COj2jTg00Cmj3eTg00DIj3bTg00Dlj6aTg00EGj3^Tg00Ejj25Tg00FFj2]Tg00Ffj2\Tg00GFj3<Tg003?j3LTg00G]j1KTg001lj2JTg00H=j3ZTg00HWj1XTg00I<j1HTg00I\j1?Tg00J;j2=Tg00Jdj3@Tg00KMj2GTg00L9j3WTg00LYj2VTg00M7j4rTg00MUj1qTg00N3j1pTg00N^j2BTg00OAj3oTg00Odj2OTg00PGj1lTg00Pij4ETg00QTj2kTg00R6j2iTg00Rbj3hTg00SAj4gTg00T3j4fTg00TNj4QTg00Thj3cTg00UEj3RTg00Ubj2UTg00VBj2NTg00V^j4mTg00W>j7nTg00Wbj7`Tg00XFj8_Tg000\R2f0R3g005PR43<p=Fg00XjR5f1R6;c3p=2AR563,U5#Hp=7f3R7f2R8'51N63'8p=6%13#1#1#1p=:%13#1p=Pg003YR9g0049R:7L3p=0P5P5P6P3Cmp=AAR563,U5p=YP5P6g00YHP3CEp=>P6g00YoR;g00ZNR<P<g00ZnR=P3g00[NFnp=;P8P;P<P<P=P6P3F`p=SP7P;P<P<P=P8P6P3G_p=D1N63,88p=d1t43As463%F3R;%I5R>/23R?P8P817>3,4?R@C6'8X02,M2P1P2P?P7P7P@C6,8;X02g00[n#[R1/C7P3P?f5RAPAP@C6,8;P0%F612>6RBf6RCPC17>6,4BC6f7RB,C1P3%F7f4RD,2>REf9RFPF17>D,4EC6g00:=RE#9RG#9#1#9#9#9#1#:#:#:#TRH/3?%PE#9#1#P#9#1#:#:#:#TR?,3@'jX02R@=e24#0RIP@P6O1#0\;^E2R;[PI\;Ab2@4g00`_PAP6EaP@PAO1#012>CRA,3HR@17>C,4A/3?RA;^3%0@%0A'8P012>BRA,3H#017>B,4A/3?#0f=,C1P312>F,3H#0f:RF,2>17>F'4/3?#0P01363#01586[R015631386#0RF[1578RA\F1]63P6n2001000000120000000X:5X;5RFP0^:5^;5R0P3PHf<RB,2>R@P8O315H@PFP0P3f>R0,2>17>0'4R0P?P7O3150?P51\55R01A63;<1P6fFRFPFP3C6'8X95,M5XD5PHP51AH3=<01PHfER@P@P3C6'8X95P?1AH?R@=<01PHfDR1P1P?C6AL0@@%K09<0@1J0@3Zf?,Y>R@#Xg00]cR0%H@'5g00^AR@g00^mR1#?RC#?R4#?R;#?,=51=5C1=51R15@55@5g00_LRC'G1=5;1=54=@515@5/GC%K@5W@3W%I@P51V58P61V57Cr%q5%p5R@%1E,B5RC1B5G5o5RG1O5?R1'>,;@%l<R<P@1O5HR4/>C,;@P<P@1B5ERE,>C,;@P5PEg00`8RCPGCE,;@5S@P<1>4E,;@P5PEPCP1CE,;@5S@CDCDCD1k@=P3P81J9:1i38#0dAh506Cgb?b@bAX65X75X851468/5?15H8147D9dA8PHP7P7P?C6[[[^65^75^85P3fAR?,7>12>?PFP8PDPBO6b>bCCfCQCQb3b1b2b1W3W2P6P3O2n2001000000121000000b5b5W=W<P6P3O2n2001000000121000000W1X02P6P3O2n2001000000121100000b4W4XB5o"). Qed.

Lemma in_runs_D_SX_RD : forall a, in_runs D_SX a -> in_runs D_RD a.
Proof.
ltac2:(KReplay.run1 (kr_t_S1Statics ()) [] "p'0h01Eh12Hah21oi001oh31Hh42H0h51ah61bh71ei011zp;2p;1p;3p;6g00=^j26Tg00a]j21Tg007mR0j1:Tg001lj25Tg003?j30Tg00PGj1;Tg00bYj12Tg00c2j23Tg00cTj69Tg00d0j24Tg00dOj67Tg00eOj68Tg00XjR1g004YR2f0R3'6f1R4,12%:1R51553f2R6,12=053P0P1f4,12=053%;1R79054#2g005PR8f6'1=057#2]1]0P4f5R9,1213135051314=057#2P51316R:A0537#2X25A05:7R:P5f3R;,31P0P1p-0P3g00emg00fIR0n10110000021000000X75g00ffP7P3E9P01403b4W3%2:ef7R:,18P2P8P:P6g00:bP4E7E8W1W0X61P3O1112;=057A0577#21189=057#2P31557O1'4W1W0n10110000021010100P3P6O2b0b21684eW1W5o"). Qed.

Lemma D_RD_slot : lookup_runs D_RD AT_SLOT_ADDR 4 = Some [1; 0; 0; 0].
Proof.
ltac2:(KReplay.run1 (kr_t_S1Statics ()) [] "p;1p;3p;2g00?Vj1:Tg007mj19Tg00<Bj14Tg00G]j13Tg00L9j32Tg00c2j28Tg001lj25Tg00I\j10Tg00gBj36Tg003?j37Tg00XjR0g00]cf032p=1%:0R1#9R2g00:=#4%30#1#1#1520,81R1'5g005Pg00h>g00^m#0#0#0#036=721do"). Qed.
Lemma D_RD_head : lookup_runs D_RD 0x120710 8 = Some (map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 0x120718))).
Proof.
vm_compute. reflexivity. Qed.

Lemma handler_rw : forall a, zwin (ly_new_handler Ly.L) (ly_new_handler Ly.L + 8) a -> in_ranges (ly_rw Ly.L) a.
Proof.
ltac2:(KReplay.run1 (kr_t_S1Statics ()) [] "h04__x1h12hih22Hah37__arithh44__ffh58__varmaph65__with71ah82lop;1p;2p;3p;4p;8p;7g00l1j1ZTg006Gj10Tg00<Bj1=Tg00@6j2DTg00lmj3UTg00Ffj2TTg00AHj1LTg00GFj3:Tg00Ejj28Tg00VBj2;Tg00@Sj23Tg00@nj2YTg00;]j15Tg003?j3CTg00G]j1@Tg001lj2ATg00H=j3STg00?Vj1OTg00LYj2NTg00MUj1MTg00N3j1KTg00Odj27Tg00N^j2JTg00Pij46Tg00OAj3ITg00PGj1HTg00XFj8GTg00QTj2FTg00R6j2PTg00Rbj3QTg00SAj4ETg00T3j4RTg00TNj4BTg00V^j4XTg00W>j7WTg00Wbj7VTf0R0#0#0p=4g00XjR1P1f1R2P0CXp=>%50#0p=2%50#5p=<%00#0#0#0p=1P2g00YoR3g00ZNR4P4g00ZnR5P0g00[NFWp=9f2R6P3P4P4P5P2P0FVp=?g00[nR7#ZR8g00:=R9#0#4#=R:,D8;U0P11T11R81>20%L7R73:f3R;,821;;0'3'3X11,Y1X81%59#2#<#2#1#1#1#=R;P11>;0=:8718;61;60'3'3X11%49#2#4#2#1#1#1#=R<1>;<R==:8718;21;2<'3R7AC8==%@89:8=1A8=3Sg00^AR=#@%O=1N12%M1%K1R=P3P4P4P5P1%<9#<#<#4#2#5#4#2#1#=R3,71R8g00YHR>1J19R9C6,9=P1P9g00`8R?171:9I18C6,9=5?=%H4P1171;P>P9C6,9=P1P9P?171<C6,9=5?=GG1F=5P0P6g003YR=g0049R5'A1P06=C=5dg00]c=Q12CEb4b5b6X0118301D3:,;0'3P7[^01P0P6P2O2b3CRCBCBW2X71o"). Qed.

Lemma handler_range : 0 <= ly_new_handler Ly.L /\ ly_new_handler Ly.L + 8 <= 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_S1Statics ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__witp;1p;2p;3p;4p;7g006Gj13Tg00<Bj14Tg00m_j2>Tg00VBj2:Tg00Ejj21Tg00nGj2LTg00ndj3BTg00G]j1@Tg00?Vj1?Tg00oHj1=Tg00MUj1<Tg00N3j1;Tg00Odj25Tg00;]j10Tg00Pij49Tg00OAj3NTg006lj1MTg00ofj3KTg00Wbj7HTg00QTj2GTg001lj2ATg00R6j2CTg003?j3DTg00Rbj3ETg00SAj4FTg00@6j26Tg00@Sj27Tg00l1j1ITg00W>j7JTf0R0#3#3p=2f1R1g00YoR2g00ZNR3P3g00ZnR4P0g00[NFJp=8g00:=R5#3R6#4R7%26R6#3#2R8#4R9'>g00]cR:/:711:91L79R;,::[[11:7R<g00emR=AB791UW011:;\=^0<g00^AR<#@%?<g00XjR<#=%<<%;<R=P2P3P3P4P<15<:g00YHR3%05#0#0#0#0#0#2#0#3#0#2#0#3#2#2#4R5,5<R2C9,8=P<%46R6,5<9N<2P315<7%M85K<C9,8=FH1G=4P0f2R=g003YR4g0049R8'A1C0==D48dAE<:1CFb2b5b611:51656/1;'7P0b1b3b4g00[n#IR0,1:1606/1;'7eo"). Qed.

Lemma relro_range : forall a, in_ranges (ly_relro Ly.L) a -> 0 <= a < 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_S1Statics ()) [] "p'0h01Hh12Hrh22hih32loh42Hah53Hinh64__x1h71eh87__arithh94__ffh:6__sat0h;6__sat1h<8__varmaph=5__with>1ai001pi011xi021zp;1p;2p;3p;6p;4p;8p;7g010Ij1[Tg00B;j2ZTg00FfR0j2MTg00GFj38Tg00@SR1j27Tg00@nR2j2ATg006Gj11Tg00<Bj1:Tg00nGj2ETg00;]j15Tg003?j34Tg011?j6CTg00m_j2VTg00VBj2<Tg00ndj3UTg00G]j1TTg00?Vj1STg00LYj2LTg00MUj1KTg00N3j1JTg00Odj2=Tg00N^j2ITg00Pij4;Tg00PGj1HTg006lj1GTg00ofj3FTg00XFj8NTg00QTj2OTg001lj2PTg00R6j2QTg00Rbj3DTg00SAj4RTg00cTj7BTg00V^j4YTg00Ejj2?Tg00W>j7XTg00Wbj7WTg00XjR3P3f1R4f0R5CYp=2f3R6f2R7'?1<45'7p=0%15#1#1#1p=6g00]cR8/?71<45'7p=31?85p=>P4g00YoR9g00ZNR:P:g00ZnR;P5g00[NFXp=9P7P9P:P:P;P4P5FWp=@g00[n#[R</Z5P2P31M33R=1245;8<R>P4P6P6P5C0'7X23,A3X33g00:=R?#1R@#:RA%1@#6R@#:RB'ERC9377P5P4f5RDPDP5C0,7>X23,A3P2P31275=8=<P7f6R2P2P5C0'7X23A322CP5f4R>/25=8=<P>f8REPEP5C0'7P112D4=8=<PDf9R1P1P4C0f:RF?3FCP5f7RG/26=8=<PEf<R<P<P>C0g011\%5?#5#1R>#1#5#5#1#6#6#6#:RH%5>#5#5#1#6#6#6#:R>'2RI121D54=g00fIR1f>RJ?3JCP412F294=IP=P3P0P3P3P3P5P5n2001100000120102102X7=PIf;R2/2GP5ECA43>GP=P3P0P3P3P3P5P4n2001100000120102102X7=PI12<EP4ECA43H<f=943HP3PHP5fCREPEP2C0A43><fERE?3EC[]1X33PHfBRIPIPFC0A43>2P3P>PHPEPEP5C0fFRE?3EC]1X23PHfDREPEP>C01VAB1<8A%>B1<8C[[%>AREg00emR2AUAB4UW4%>C\2^4Eg00^ARE#T%SE1L34%K3%J3REP9P:P:P;P31=3Hg00YHR91I3?R?C;,9EP3P?g00`8R21=3>C;,9E5@E%H:P31=38P9P?C;,9EP3P?P21=3A%G@5F3C;,9E5@EGN1OE;P5P7g003YREg0049R;'P1Q57=4E;dAD384CRb9b<b=X63PHP5P5P>C0A344C[^63P5fHP6O2b8b:b;W1P<P5P4FBW0W1PJP5PDFBW0P5O1b0P5O1b0W5P5O1P1f@RD?3DCP5n010000000X01P5O1n200100000021100010000W1W5P4P5O2n2001000000121000000W0X23P4P5O2n2001000000121101000W0X33P4P5O2n2001000000121101000W0X>3o"). Qed.

Definition S1ST : StaticsIface Ly.SEGS Ly.L :=
  drv_statics Ly.SEGS Ly.L D_SX D_SX_rw handler_rw handler_range relro_range.

Lemma s1_region : forall a,
  sx_region S1ST a <-> (in_runs D_SX a \/ zwin (ly_new_handler Ly.L) (ly_new_handler Ly.L + 8) a).
Proof.
ltac2:(KReplay.run1 (kr_t_S1Statics ()) [] "h01ap;2p;1p;3p;4g00=^j27Tg00l1j16Tg006Gj10Tg00<Bj11Tg00@6j25Tg00lmj34Tg011\j23Tg0126j42Tg00Xjp-0g012dg013=g004Yf0R0'7g00[n#6R1g00:=#0#0#0#1,51;40'3C2W0o"). Qed.

