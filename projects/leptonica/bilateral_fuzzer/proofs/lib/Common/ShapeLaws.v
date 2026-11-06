(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_ShapeLaws () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indK47Corelib4Init5Logic3and01C59OSSVerify5KrLib6Common8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib6Common8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c59OSSVerify5KrLib6Common9ShapeLaws<t_alt2_assocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib6Common8ShapeAlg5t_nilC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z4landC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_and_unsignedC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib6Common8ShapeAlg>t_emit_has_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common9ShapeLaws>bv_and_255_litC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_alt2_assoc : forall A B C : TSet, t_eq (t_alt2 (t_alt2 A B) C) (t_alt2 A (t_alt2 B C)).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) [] "h01Hh12H0h21Ah31Bh41Ch52trp;1p;2p;3p;6p;4p10000p4p70R0p1000^p4p7210p8P0p1001:p4p710p8g001Xj19Tg0028j20Tg002Rj33Tg002lj31Tg003Fj64Tg003bj48Tg004=j22j35Tg0058j26Tg005Qj27Tg006JR0g007C#9f3R1f0R2O1R3f2R4P2O1R5'0f1R6P2O1R7'0R8f4R9P6O1R:P1P6O1R;P4P6O1R<'0R='0R>[1057,03R310:;R;/0<R7[P;P<P>f5R>P4O1R5P9P4O1R?P1P4O1R@,0?RA,05f6P1O1RBP>P1O1R>P9P1O1R9'0RC;32X05A3>9291BCX0?P2E4X1;A1?@2915AX1<P2E4X08P:P=P7105?R7A35?273@X1:P?P@107@10B>R7A1B>2739X0?A1792X0@P2E4X1=P2E4X03C81214?5621246R3=512'6eW512321262,24'7eX40X30W2o"). Qed.

(* [comment removed for export] *)
Lemma t_alt2_absorb : forall A B : TSet, t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) [] "h01Hh12H0h21Ah31Bh42trp;1p;2p;3p;6p;4g001Xj19Tg0028j20Tg002Rj33Tg002lj31Tg003Fj64Tg003bj48Tg004=j22j35Tg0058j26Tg005Qj27Tg006JR0g007C#9f2R1f0R2O1R3f1R4P2O1,03R3'0R5f3R6P4O1R7P1P4O1R8'0R9[1079R:\3P7P9P9f4R;P1O1R<P6P1O1R=;32X17P<P=10<=R>f5P6O1R?P;P6O1R6;32X0<A1?62X0=P2E4X19P2E4X05P7P8P:A3<>2X17A1<=291<>X18P2E4X03C81214=512A5142'6eW41242R2,24/72eX30W2o"). Qed.

(* [comment removed for export] *)
Lemma t_alt3_as_alt2 : forall A B C : TSet,
  t_eq (t_alt2 A (t_alt2 B C)) (t_alt2 (t_alt2 A B) C).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) [] "h01Ah11Bh21Cp;2p;3g004=j20Tg0089j32Tg009;j31Tg006JR0f2R1f1R2'0f0R3'01023,01A212331X20X10W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_alt2_emit_nil_l : forall (e : list event) (T : TSet),
  T [] -> t_eq (t_alt2 (t_emit e t_nil) (t_emit e T)) (t_emit e T).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) [] "p'0h03tr'h11Hh22trh32H0h42H1h52Hph61Th71ei001xp;1p;3p;2p;4p;6g001Xj1GTg00:8j1FTg00:Xj34Tg00;2R0j20Tg0028R1j28Tg00;MR2j26Tg002Rj3>Tg00;gj2=Tg003bj49Tg00<Aj4ETg002lj3<Tg001:j6;Tg00<[j27j3CTg004=j3Dj2ATg0058j2@Tg005Qj2BTg00=Vj3?Tg00>Lj3:Tg007CR3f1R4f0R53?p=2f3R6f2R7A:34534p=31645,87p=1A:345p=5%G3R8g006JP5%F3R3O11256R9P8P4f4R:P5C3R;A4853R<'0X08718P6P5O1,0;X089198R9'8R;124:R=P8P7f5R>P5C3R?P:P5O1'0X08718R@[10?<X0891=8R=/8@\9P1P=P@127>R?P8P6f6RAP5C3RBP>P5O1'0X08718RCP510B<X0891?8P1126AP8P:f7R1P5C3/0<X08,6812:1R?P8P>f8RBP5C3RDP1P5O1'0X08718P512>BP8PAf9REP5C3RFPBP5O1'0X08,68;>5X5?P5O110D<X08,68P2P810F<X0812AEP8P1f:R1P5C3PEP5O1'0X08718P5P8PBf;RBP5C3/0<P0P8PEf<REP4C3A4843f=R0,21P8PBf>R1P5C3P0P5O1'0X08718P5P8PBP1P6C3P8f?RB/5:A48>3fAR0,24fBR</55RA9487P0P5O1RF'0X08718[X28A48:3P8P31505R:/2015<4=48A/0FX08718X08f@RF/53RA/2F1503=48:PFP5O1'0X08RF,68P8PFP3A48AAPBP3O11=8AP1C9CE3<P>P5E;W1PEP5E;W1P4P5O2n2001000000120000000W1X08P4P5O2n2001000000121100000W1P5O1n200100000021000011000W1P5O1P5X1CP5O1n200100000021100010000X4;A<=@5X19C9g00>iR9,761767;D5AC675'@eX2817791774R7'A/B7eW3W6W7o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_alt2_distr : forall (e : list event) (A B : TSet),
  t_eq (t_emit e (t_alt2 A B)) (t_alt2 (t_emit e A) (t_emit e B)).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) [] "p'0h03tr'h11Hh22trh32HAh42HBh52Hph61Ah71Bh81ei001xp;1p;2p;3p;4p;6g001Xj1GTg00;2R0j20Tg0028R1j21Tg00;MR2j25Tg002Rj3<Tg00:Xj38Tg00;gj2@Tg003bj4:Tg00<Aj4=Tg002lj39Tg001:j6?Tg004=j2>j3ETg00<[j3Fj2;Tg0058j2DTg005Qj2CTg00=Vj3BTg00>Lj3ATg007CR3f1R4f0R53Bp=4f3R6f2R7AA34538p=31145,07p=61545,17p=2AA345p=7%G3R3g006JR81456R9P3P4f4R:P5C3R;P6P5O1R<P7P5O1R=36X03723R>144:R?P3P7f5R@P5C3RAP:P5O1RB'0X03723RC10A<X0392?3RD'1[10;<X03929310;=X039293'1R9A6AB<X03,53RA,1?[P1P?PA147@RAP3P6f6R?P5C3R<P@P5O1R='0X03723R;10<BX0392A3RE'1P5146?RFP3P:f7RGP5C3RHP?P5O1RI'0X03,53RJ'110H=X03,53RK,1FA<FJ53<X5AP5O1A6<=BX03,53R<P2P3A6HI=X0314:GRHP3P@f8R=P5C3RBPGP5O1RL'0X03,53RM'110BIX03,53RN,1H'1P5P3P?f9ROP5C3RPP=P5O1RQ;6LRRP0P3PGf:RSP4C3POP4O1P=P4O1'1f;RT,4=RUP3POf<RVP5C3RWPTP5O1'0X03723PSP5O1RX,0WX0392U3'1P5P3POPVP6C3P3f=RU/7:PUP@O1RWPVP@O1RY'1f?RZ,44R[f@R\/75R]9837R^PZP5O1R_'0X03723f>R`P5O1Ra,0^X0392[3'1[X23PVP:O1PTP:O1'1P1PWPY17Z?/4ZRY17\GRW=83]R]/0_X0372310]aX0392Y3'1P5P`P?O114W\RYfAR]/7=17]5Ra583R[P\P5O1R^'0X03Rb,53Rc'1Rd10[_X03R[,53Re,1YRfP3PbPGA83WWRbPZPGO11@3WRWP5C:C=99Yc3<W3P5O1PUP?O1P3P[PGPbP`PGO1PWP5C:C=99Ye99dfW4P5O1n200100000021000010000W1PSP5E?W1P4P5O2n2001000000121000000W1X03P4P5O2n2001000000121100000W1P5O1n200100000021000011000X1>P1PCPD11A<P5P1PFPJA6BLIX0392H3RBP514@=PRX03,53;<5X5HP5O1RHP2P310PQX0314?OP3PGPSP5C3POP5O1RG;6QX03723RQP5P3P=PTP5C3R=/0XP0P3POPVP4C3ROPTP4O114SUP3PTP`P5C3PUP5O1PVP5O136X03723RXP5P3PTP`P6C3RTP317Z:RRPZP@O1RZ144]P3P7fBP5C3P]P5O1;6^X03723RI[X23P`P:O117\@RJ/4\R\17]?=83a?6^_X03R^,53R_P3P^P@A83JJRaP`P@O1R`,1ZR]1@3JRJA<Z`5C:C=39W3PVP5E?W1P4P5O2n2001000000120000000W1X03P4P5O2n2001000000120100000X1MP5O1n200100000021000011000X1;P5O1P1PFPKPBP5PHP2P310PLX03PQP510=GP0POPSP4O1PXP5P3PRPI\`X23PUP:O1P3P^P@PaP]PJA9Z`5C:C=99\_W4PVP5E?X1TP4P5O2n2001000000120000000W1X03P4P5O2n2001000000120100000X1NP5O1n200100000021000011000X1EP5O1n200100000021100011000X19C:1>74=F651;671;64;E5'DeX231>45,;71;741;75'>'CeX78W6W8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bv_and_255_lit : forall c, (0 <= c < 256)%Z ->
  bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) = Z_to_bv 64 c.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) [] "h01zh11Hh22H0h32Hah47__arithh54__ffh68__varmaph75__with84__x1h96__sat0h:6__sat1h;2b1h<2b2h=1nh>2Hch?1cp;1p;2p;3p;4p;7p;8p;6g00?cj14Tg00@Hj1:Tg00@fj20Tg00;2R0j29Tg00ABj1=Tg00:Xj3;Tg00Aej22Tg00BOj3PTg00C3j1ETg00CQj2BTg00D7j15Tg00D\j3dTg00EAj27Tg00E_j2CTg00FEj2ITg00Fbj2ZTg00GBj2GTg00Gjj3FTg00:8j1YTg001Xj1XTg00HNj2WTg00Hlj1VTg00IJj1UTg00J5j2RTg00JXj2<Tg00K;j1OTg00K]j3DTg00L@j2NTg00;gj2MTg00Lbj2QTg00MNj3LTg00Mmj4STg00N_j3TTg00OBj1cTg00O`j1bTg00P>j3aTg00Paj3KTg00QMj2JTg00R<j3^Tg00Rjj2]Tg00SFj4HTg00T1j7\Tg00TUj7[Tg00U9j8_Tg001:j6`Tg00U]R1f0R2']p=1g00V;R3f1R4;;2p=3P3P4g00VYP2CHp=?P4g00W@R5g00W_R6P6g00X?R7P2g00X_F\p=6P3P4g00Y?P2CHp=Af2R8P5P6P6P7P4P2F[p=@f3R9P5P6P6P7P8P4P2G_p=>P3f4R5P9P8P4P2E`p=8%12g00YfR:#4R;#4#4R<#4#4#4R=#4#4#:R>,02R?'9g00ZKR@%=2RA%=4RBP0%=8?;4212981294'3RC[12841282'3%=9?;84[RD%=5?;98\CAP842P2n2001000000120000000W<W;W=PD^<B^;A^=@P2%E=R@1B@8RA%5:#5#5#5#5#5#5#:RB,B@RD5d@RCPA12@ARE12@DRF'71B@9,2@,32X031C@8RG172F/32X031C@BRH1C@9RI/72/3IX03P8172H/32X03PB1792/39X03%:;R;%:<RI'IRJ,Z81329X031G;I101;RK%1IRL101J[[%1;RMg00ZiRNAF;I4UW3%1J\N^3MP0%15RO105>R5f5RP#1RQ10PJ'9P9f6#1RRf7/0>RSg00[ERT#YRU%XTRT1W34RV%V3RW%U3RX1R3:R:1<3>'?,6XRY%O6R6PX1<31RZ/A:,6XR[P61<3;R\%E<5D3,?:,6X9@X[C>C>1NX7R7P2P8g00\1R<g00\QR]'M1Q28=;<]dAL314CSR]b5b6b7X83%14R<%18R^108J'9[\?^83P2f9P4P8O3R_b4W2W1P4P2O2n2001000000120000000b9b:9T8J%cI,78P0P^108>PLP410P>PUPT%b3R>PW1<3I,AZ,6XP7P]b5b6b7PLP2b4W2X1OP4P2O2n20010000001200000009a8ID8PH%:=R=,G;RH%1=1I;=RI,01[\KRKAF;=4VNX3MR=%1I\N^3MRMP0POP5%1B10BI'9RNP9PUPTP>PW1<3BR>,AZ,6XAD3\@R\,?>,6X5@XP7P]b5b6b7PNP2b4X2SX1RP4P2O2n2001000000120000000b9b:9K@BD8PGPHPKP=PMP0POP510PI,9QP9PUPTPVPWPXPYP6PXP[P61?:\,6X9@X[C>C>P7P]b5b6b7X83108I,9^\<\?^83P_b4X2SX1RP4P2O2n2001000000121000000b9b:9K@8D8PF1J@BD8PE1J@8D812@CA^@ADD8O4b1W>X?3o"). Qed.

(* [comment removed for export] *)
Lemma exit_leaf_eq : forall (ch : word) c fs, (0 <= c < 256)%Z ->
  t_eq (t_emit (map (WriteEv ch) []) (t_exit (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) fs))
       (t_exit (Z_to_bv 64 c) fs).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) [] "h02Hch11bh21ch32chh42fsp;1p;2p;4p;3p;6g00?cj10Tg00C3j17Tg00ABj18Tg00Rjj2<Tg00@Hj1:Tg00@fj2DTg00;2j2>Tg00CQj22Tg00]1j15Tg00:8j16Tg000^j44Tg00]gj23j3BTg00<[j29Tg005Qj2;Tg00^bj2FTg00_Xj3ETg00`8j2CTg00a;j2?Tg00D7j11Tg00D\j3@Tg00b=j2ATg001:j6=Tg00YfR0#0#0#0R1#0#0#0R2#7R3#8R4g00V;g0000g00U]f1R5'<%02#0#:,D5'>P4f2R2,23R6%71#8R1g007CR7f4#5%61R8C4f0R9/32'9f3R:,23/32';X141365R41F65%67R;5E7g00>i'CAB65;e'?P1P7%5:P8C4/94/;4e%10#1#1#1#1#1#1#:,239@361A29E=W0W4W2W3o"). Qed.
