(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmModel PmStatics PmSpecs PeCLayout PeCSink PeCStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeCModel () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic8eq_ind_rc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCModel3PEC9mode_codeC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode00C13~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode02C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode09C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode0:C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode0;C13~~~C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic4True01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums8positive00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L55rangeC13~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List3revC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:length_revC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCModel3PEC8stk_convC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef6pstate00C13~~~I47Corelib4Init9Datatypes3nat00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM6pstate00C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCModel3PEC7ps_convC13~~~K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List7map_appI47Corelib4Init9Datatypes4prod00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM:parser_ownC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCModel3PEC7enc_ownC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK8sink_ownC13~~~C46Stdlib5Lists4List9app_assocc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCModel3PEC5ownedC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM3pst00C13~~~i89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCModel3PEC3enc00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK4sink00C13~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCModel3PEC4ecapC13~~~C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z7pow_1_rC56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op201".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition b2z (b : bool) : Z := if b then 1 else 0.
(* [comment removed for export] *)
Definition mode_code (m : pmode) : Z :=
  match m with
  | Mroot => 0 | Maccept => 1 | Marray => 2 | Miarray => 3 | Mtarray => 4 | Mkey => 5 | Mval => 6 | Mtkey => 7 | Mtval => 8 | Mikey => 9 | Mival => 10
  end.
Definition ps_conv (t : UbjRef.pstate) : PM.pstate := PM.PS (mode_code (ps_mode t)) (ps_len t) (ps_type t) (ps_idx t).
(* [comment removed for export] *)
Definition stk_conv (stk : list UbjRef.pstate) : list PM.pstate := map ps_conv (rev stk).
(* [comment removed for export] *)

Lemma mode_code_range m : 0 <= mode_code m <= 10.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCModel ()) [] "p'0h07__arithh14__ffh28__varmaph35__with41mi001pp;1p;2p;3p;4p;7p10000p4p710p1000Mp4p710p8p1000ip4p7210p1001Fp4p710p8g001dj11Tg0035j18Tg003Zj19Tg004?j12Tg004]j1JTg005=j1DTg005]j1ATg006;j1?Tg006Yj1>Tg007Dj2<Tg007gj2LTg008Ij2KTg008cj2ITg009Oj3HTg009ij3GTg00:Hj4CTg00;:j25Tg00;Vj2:Tg00<1j46Tg00<\j77Tg00=@j7;Tg00=dR0f2R1'5f1R2f0R3'5':p=0g00>BR4/<3p=3P1g00>`R5g00??R6P6g00?_R7P4P2g00@?R8P3C6g00@fR9F7p==f4R:P5P6P6P7f3R;P5P6P6P7P4P1P8P2C6P9F7P3F;p=M1503p=Bf6P5P6P6P7f5P5P6P6P7P4P:P8P;C6P9F7P1P5P6P6P7P4P2P8P3C6P9F7F;p=4P4P2P8P3C6p=@P;P5P6P6P7P1P2P5P6P6P7P3P9F7F;p=E1523,:1p=Fg00AFR9P9%13R6g00BTR5#8R;#9R8#8#2R:706P3g00C9R6#JR<%D6R6%A4R=%?4R>%>4R?P?1<40R@P@%3:RA9=?@RBDM1L?7R7P3P1g00CeRCg00DERD'K1I31=HCDdAG402CCR4b1b2b31500%B:R0':P3b0g00De#1R2?02:eP<P6P=P>P?P?P@%25R2#3RDP?PDPAF4P7P4b1b2b3A022:P3b0g00F3#1R2?02:eP<P6P=P>P?P?P@%2;R2#3RDP?PDPAF4P7P4b1b2b3A022:P3b0g00GA#1R2?02:eP<P6P=P>P?P?P@%95R5#2R2#3RDP?PDPAF4P7P4b1b2b3A022:P3b0g00HO#1R2?02:eP<P6P=P>P?P?P@%8;R;#2R2#3RDP?PDPAF4P7P4b1b2b3A022:P3b0g00I]#1R2?02:eP<P6P=P>P?P?P@%28R8#3R2P?P2PAF4P7P4b1b2b3A088:P3b0g00Jk#1R8?08:eP<P6P=P>P?P?P@%85#2R8#3R2P?P2PAF4P7P4b1b2b3A088:P3b0g00L9#1R8?08:eP<P6P=P>P?P?P@%95#2R5#3R8P?P8PAF4P7P4b1b2b3A055:P3b0g00MG#1R5?05:eP<P6P=P>P?P?P@%8;#2R5#3R8P?P8PAF4P7P4b1b2b3A055:P3b0g00NU#1R5?05:eP<P6P=P>P?P?P@%9;#2R;#3R@P?P@PAF4P7P4b1b2b3A0;;:P3b0g00Oc#1R;?0;:eP<P6P=P>P?PBP?1@AACEP7P4b1b2b3AF0::P3b0g00Q1#1R0?00:en01100000;0000000000000000000000X49P3O1W4o"). Qed.
Lemma mode_code_inj m m' : mode_code m = mode_code m' -> m = m'.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCModel ()) [] "p'0h01Hh12H0h21eh31mh42m'i001pi011zp;1p;3p;2p;6g001dj14Tg009Oj31Tg008Ij25Tg004?j1:Tg00R?j22Tg0035j1;Tg003Zj1<Tg000Mj6=Tg00>BR0f1R1f0R231p=0g00=dR3=102p=9P0P3f2R4g00R^R5P1P2E=p=7A1023p=6P0P4P1P5P3P2E=p=8P0f3P4P5P1P2E=p=3g00AFR5P5%42R6%41'0A1514[P1P5g00DeR4#4R7/06A1541[P2A10331554W01077A1544[eg00BTR3#:R8#9P0p-0R9P2g00S:R:g00SVR;P;n011010003001000010000X20R<?782P;g00F3R=9154R>/22b1W0%4=R?,07P>[e%;3R>#:R@#9A7<@2P;g00GARA9154RB/22b1W0%4ARC,07PB[e%<3R3#:RB#9A7<B2P;g00HORD9154RE/22b1W0%4DRF,07PE[e%;>RE#:RG#9A7<G2P;g00I]RH9154RI/22b1W0%4HRJ,07PI[e%<>R>#:RI#9A7<I2P;g00JkRK9154RL/22b1W0%4KRM,07PL[e%;3#:RL#9A7<L2P;g00L9RN9154RO/22b1W0%4NRP,07PO[e%<3#:R3#9A7<32P;g00MGRO9154RQ/22b1W0%4ORR,07PQ[e%;E#:RQ#9A7<Q2P;g00NURS9154RT/22b1W0%4SRU,07PT[e%<E#:RE#9A7<E2P;g00OcRT9154RV/22b1W0%4TRW,07PV[e%;>#:R>#9A7<>2P;g00Q1R<9154RV/22b1W0%4<RX,07PV[en01100000;0000000000000000000000P510?6A15=1[P2%68P0P9P2P;P:P;n011010003001000010000X20RV=882P;A15=4RY/22b1W010?7PY[e1088155=W010??A15==[e108@P8P0P9P2P;g00T3RYP9P2P;P;P:n011000003100001000000RZP;n011010003001010010100X20R[P@P2C3P;A15=AR\/22b1W010?CP\[e108BP8P[PBP2C3P;A15=DR\/22b1W010?FP\[e108GP8P[PGP2C3P;A15=HR\/22b1W010?JP\[e108IP8P[PIP2C3P;A15=KR\/22b1W010?MP\[e108LP8P[PLP2C3P;A15=NR\/22b1W010?PP\[e1083P8P[P3P2C3P;A15=OR\/22b1W010?RP\[e108QP8P[PQP2C3P;A15=SR\/22b1W010?UP\[e108EP8P[PEP2C3P;A15=TR\/22b1W010?WP\[e108>P8P[P>P2C3P;A15=<R[/22b1W010?XP[[en01100000;0000000000000000000000P510C6A15A1[P2%6@A8@V2P;A15A4R[/22b1W010C7P[[e10@8P@P0P9P2P;PYP9P2P;P:P;n011000003100001000000R[P;n011010003001010010100X20R\P8P2C3P;A15A=R]/22b1W010C?P][e10@@155AW010CCA15AA[e10@BP@P\PBP2C3P;A15ADR]/22b1W010CFP][e10@GP@P0P9P2P;PYP9P2P;PZP;n011000003101001010000R]P;n011010003001010010100X20R^PGP2C3P;A15AHR_/22b1W010CJP_[e10@IP@P\PIP2C3P;A15AKR_/22b1W010CMP_[e10@LP@P^PLP2C3P;A15ANR_/22b1W010CPP_[e10@3P@P\P3P2C3P;A15AOR_/22b1W010CRP_[e10@QP@P^PQP2C3P;A15ASR_/22b1W010CUP_[e10@EP@P\PEP2C3P;A15ATR_/22b1W010CWP_[e10@>P@P^P>P2C3P;A15A<R^/22b1W010CXP^[en01100000;0000000000000000000000P510F6A15D1[P2%6BA8BV2P;A15D4R^/22b1W010F7P^[e10B8PBP0P9P2P;PYP9P2P:P;P;n011000003100001000000R:P;n011010003001010010100X20R^P8P2C3P;A15D=R_/22b1W010F?P_[e10B@PBP^P@P2C3P;A15DAR_/22b1W010FCP_[e10BB155DW010FFA15DD[e10BGPBP^PGP2C3P;A15DHR_/22b1W010FJP_[e10BIPBP0P9P2P;PYP9P2PZP;P;n011000003101001010000RZP;n011010003001010010100X20R_PIP2C3P;A15DKR`/22b1W010FMP`[e10BLPBP^PLP2C3P;A15DNR`/22b1W010FPP`[e10B3PBP_P3P2C3P;A15DOR`/22b1W010FRP`[e10BQPBP^PQP2C3P;A15DSR`/22b1W010FUP`[e10BEPBP_PEP2C3P;A15DTR_/22b1W010FWP_[e10B>PBP^P>P2C3P;A15D<R_/22b1W010FXP_[en01100000;0000000000000000000000P510J6A15H1[P2%6GA8GV2P;A15H4R_/22b1W010J7P_[e10G8PGP\P8P2C3P;A15H=R_/22b1W010J?P_[e10G@PGP0P9P2P;PYP9P2P;P[P;n011000003101001010000R_P;n011010003001010010100X20R`P@P2C3P;A15HARa/22b1W010JCPa[e10GBPGP\PBP2C3P;A15HDRa/22b1W010JFPa[e10GG155HW010JJA15HH[e10GIPGP\PIP2C3P;A15HKRa/22b1W010JMPa[e10GLPGP`PLP2C3P;A15HNRa/22b1W010JPPa[e10G3PGP\P3P2C3P;A15HORa/22b1W010JRPa[e10GQPGP0P9P2P;PYP9P2P;P]P;n011000003101001010000P;n011010003001010010100X20PQP2C3P;A15HSRa/22b1W010JUPa[e10GEPGP\PEP2C3P;A15HTRa/22b1W010JWPa[e10G>PGP`P>P2C3P;A15H<Ra/22b1W010JXPa[en01100000;0000000000000000000000P510M6A15K1[P2%6IA8IV2P;A15K4Ra/22b1W010M7Pa[e10I8PIP^P8P2C3P;A15K=Ra/22b1W010M?Pa[e10I@PIP^P@P2C3P;A15KARa/22b1W010MCPa[e10IBPIP0P9P2P;PYP9P2P[P;P;n011000003101001010000R[P;n011010003001010010100X20RaPBP2C3P;A15KDRb/22b1W010MFPb[e10IGPIP^PGP2C3P;A15KHRb/22b1W010MJPb[e10II155KW010MMA15KK[e10ILPIP^PLP2C3P;A15KNRb/22b1W010MPPb[e10I3PIPaP3P2C3P;A15KORb/22b1W010MRPb[e10IQPIP^PQP2C3P;A15KSRb/22b1W010MUPb[e10IEPIP0P9P2P;PYP9P2P]P;P;n011000003101001010000P;n011010003001010010100X20PEP2C3P;A15KTR]/22b1W010MWP][e10I>PIP^P>P2C3P;A15K<R]/22b1W010MXP][en01100000;0000000000000000000000P510P6A15N1[P2%6LA8LV2P;A15N4R]/22b1W010P7P][e10L8PLP\P8P2C3P;A15N=R]/22b1W010P?P][e10L@PLP0P9P2P;PYP9P2P;P:P;n011000003101001010000P;n011010003001010010100X20R]P@P2C3P;A15NARb/22b1W010PCPb[e10LBPLP\PBP2C3P;A15NDRb/22b1W010PFPb[e10LGPLP]PGP2C3P;A15NHRb/22b1W010PJPb[e10LIPLP\PIP2C3P;A15NKRb/22b1W010PMPb[e10LL155NW010PPA15NN[e10L3PLP\P3P2C3P;A15NORb/22b1W010PRPb[e10LQPLP]PQP2C3P;A15NSRb/22b1W010PUPb[e10LEPLP\PEP2C3P;A15NTRb/22b1W010PWPb[e10L>PLP0P9P2P;PYP9P2P;PZP;n011000003101001010000P;n011010003001010010100X20P>P2C3P;A15N<RZ/22b1W010PXPZ[en01100000;0000000000000000000000P510R6A15O1[P2%63A83V2P;A15O4RZ/22b1W010R7PZ[e1038P3P^P8P2C3P;A15O=RZ/22b1W010R?PZ[e103@P3P^P@P2C3P;A15OARZ/22b1W010RCPZ[e103BP3P0P9P2P;PYP9P2P:P;P;n011000003101001010000P;n011010003001010010100X20R:PBP2C3P;A15ODRZ/22b1W010RFPZ[e103GP3P^PGP2C3P;A15OHRZ/22b1W010RJPZ[e103IP3P:PIP2C3P;A15OKRZ/22b1W010RMPZ[e103LP3P^PLP2C3P;A15ONRZ/22b1W010RPPZ[e1033155OW010RRA15OO[e103QP3P^PQP2C3P;A15OSRZ/22b1W010RUPZ[e103EP3P:PEP2C3P;A15OTR:/22b1W010RWP:[e103>P3P^P>P2C3P;A15O<R:/22b1W010RXP:[en01100000;0000000000000000000000P510U6A15S1[P2%6QA8QV2P;A15S4R:/22b1W010U7P:[e10Q8PQP\P8P2C3P;A15S=R:/22b1W010U?P:[e10Q@PQP`P@P2C3P;A15SAR:/22b1W010UCP:[e10QBPQP\PBP2C3P;A15SDR:/22b1W010UFP:[e10QGPQP0P9P2P;PYP9P2P;P_P;n011000003101001010000P;n011010003001010010100X20PGP2C3P;A15SHR:/22b1W010UJP:[e10QIPQP\PIP2C3P;A15SKR:/22b1W010UMP:[e10QLPQP`PLP2C3P;A15SNR:/22b1W010UPP:[e10Q3PQP\P3P2C3P;A15SOR:/22b1W010URP:[e10QQ155SW010UUA15SS[e10QEPQP\PEP2C3P;A15STR:/22b1W010UWP:[e10Q>PQP`P>P2C3P;A15S<R`/22b1W010UXP`[en01100000;0000000000000000000000P510W6A15T1[P2%6EA8EV2P;A15T4R`/22b1W010W7P`[e10E8PEP^P8P2C3P;A15T=R`/22b1W010W?P`[e10E@PEP^P@P2C3P;A15TAR`/22b1W010WCP`[e10EBPEPaPBP2C3P;A15TDR`/22b1W010WFP`[e10EGPEP^PGP2C3P;A15THR`/22b1W010WJP`[e10EIPEP0P9P2P;PYP9P2P_P;P;n011000003101001010000P;n011010003001010010100X20PIP2C3P;A15TKR_/22b1W010WMP_[e10ELPEP^PLP2C3P;A15TNR_/22b1W010WPP_[e10E3PEPaP3P2C3P;A15TORa/22b1W010WRPa[e10EQPEP^PQP2C3P;A15TSRa/22b1W010WUPa[e10EE155TW010WWA15TT[e10E>PEP^P>P2C3P;A15T<R^/22b1W010WXP^[en01100000;0000000000000000000000P510X6A15<1[P2%6>A8>V2P;A15<4R4/22b1W010X7P4[e10>8P>P\P8P2C3P;A15<=R=/22b1W010X?P=[e10>@P>P]P@P2C3P;A15<ARA/22b1W010XCPA[e10>BP>P\PBP2C3P;A15<DRD/22b1W010XFPD[e10>GP>P]PGP2C3P;A15<HRH/22b1W010XJPH[e10>IP>P\PIP2C3P;A15<KRK/22b1W010XMPK[e10>LP>P0P9P2P;PYP9P2P;P[P;n011000003101001010000P;n011010003001010010100X20PLP2C3P;A15<NRN/22b1W010XPPN[e10>3P>P\P3P2C3P;A15<ORO/22b1W010XRPO[e10>QP>P]PQP2C3P;A15<SRS/22b1W010XUPS[e10>EP>P\PEP2C3P;A15<TRT/22b1W010XWPT[e10>>155<W010XXA15<<[en01100000;0000000000000000000000n01100000;0101010101010101010101X45X35P1P2O2X45W3o"). Qed.
Lemma stk_conv_length stk : length (stk_conv stk) = length stk.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCModel ()) [] "h03stkh11np;1p;2p;3p;6p;4p100TXp4p70p100Ubp4p710p8g005=j19Tg00V?j28Tg00VWj20Tg009Oj31Tg008Ij27Tg00W7j24Tg001Fj62Tg00WVj43Tg00X2j45Tg00XQj16Tg00YaR0#9R1g00[0R2f0R3,80R4,00R5f1,009123X12R6P21003R7P61727P51403E2g00[OR5P0P5g00\]R6P4C3'0P0P5P6P4C5E2%63,05=127eX01P3O1W0o"). Qed.
Lemma stk_conv_cons t r : stk_conv (t :: r) = stk_conv r ++ [ps_conv t].
Proof.
ltac2:(KReplay.run1 (kr_t_PeCModel ()) [] "h01rh11th21lp;1p;2p;3p;5p;6p;4g005=j16Tg00V?j24Tg004]j15Tg00]lj32Tg00Ubj30Tg00\]R0j18Tg009Oj33Tg008Ij2<Tg00^Lj5;Tg001Fj69Tg00XQj17Tg00WVj4:Tg00YaR1g00[OR2P0f0R3C:p=1%61R4%62R51413R6#1R7f1R8%51521R9#15021418#1f2#8%52R:5225029353X25%88=22:R:9027R7,<5A0169#1P1P2P0P6P9D;E9A2183R9,41#1=357e%79%73=02:535eX04X11P8P3O2W0X11o"). Qed.

Section WithImage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable E : pe_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.

Abbreviation parser_at := (PM.parser_at segs A acc ann).
Abbreviation iss_at := (PM.iss_at segs A acc).
Abbreviation sink_at := (PESK.sink_at segs L acc ann).

(* [comment removed for export] *)
(* [comment removed for export] *)
Record enc : Type := ENC { en_b : Z; en_k : Z; en_stk : list UbjRef.eitem (* [comment removed for export] *); en_depth : Z }.
Definition ecap (k : Z) : Z := if k =? 0 then 0 else 2 ^ (k - 1).
Definition ESZ : Z := 24.
Definition enc_own (en : enc) : list (Z * Z) := if en_k en =? 0 then [] else [(en_b en, ESZ * ecap (en_k en))].

Definition eitem_at (M : word -> option byte) (a : Z) (e : UbjRef.eitem) : Prop :=
  L5.u32_at segs M a (ei_kind e) /\ L5.u64_at segs M (a + 8) (ei_len e) /\ L5.u64_at segs M (a + 16) (ei_cnt e).

Definition enc_at (M : word -> option byte) (ov fb : Z) (en : enc) : Prop :=
  L5.u64_at segs M ov (pe_vt E) /\ L5.u64_at segs M (ov + 8) (PESK.o_sink E fb) /\ L5.u32_at segs M (ov + 16) UbjRef.MAX_DEPTH
  /\ L5.u64_at segs M (ov + 24) (en_b en)
  /\ L5.u64_at segs M (ov + 32) (en_b en + ESZ * Z.of_nat (length (en_stk en)))
  /\ L5.u64_at segs M (ov + 40) (en_b en + ESZ * ecap (en_k en))
  /\ L5.u32_at segs M (ov + 48) (en_depth en)
  /\ L5.defined M ov 56 /\ acc M ov 56
  /\ 0 <= en_k en <= 12 /\ Z.of_nat (length (en_stk en)) <= ecap (en_k en) /\ 0 <= en_depth en <= UbjRef.MAX_DEPTH + 1
  /\ (en_k en = 0 -> en_b en = 0)
  /\ (0 < en_k en ->
        en_b en mod 8 = 0 /\ L5.defined M (en_b en) (ESZ * ecap (en_k en)) /\ block_range L (en_b en) (ESZ * ecap (en_k en))
        /\ acc M (en_b en) (ESZ * Z.of_nat (length (en_stk en)))
        /\ ann M (en_b en) (ESZ * Z.of_nat (length (en_stk en))) (ESZ * ecap (en_k en)))
  /\ (forall i, (i < length (en_stk en))%nat -> eitem_at M (en_b en + ESZ * Z.of_nat i) (nth i (en_stk en) (EI 0 0 0))).

(* [comment removed for export] *)
Definition enc0 : enc := ENC 0 0 [] 0.

(* [comment removed for export] *)
Definition pot_estack (k : Z) : credit :=
  (hl_k_per_malloc L * (12 - k), ESZ * (2 ^ 12 - 2 ^ k) + (12 - k) * hl_b_overhead L).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pos_of (p : list Z) (src : PM.srcst) (sm : PM.strm) : Z := blen p - PM.unread src sm.
Definition content_ok (M : word -> option byte) (fb : Z) (p : list Z) (src : PM.srcst) (str : PM.vstr) (sm : PM.strm) : Prop :=
  PM.vs_size str = blen p
  /\ L5.bytes_at segs M (PM.vs_data (PMSP.o_is A fb + 80) str) p
  /\ 0 <= pos_of p src sm
  /\ L5.bytes_at segs M (PM.sr_de src) (UbjRef.slice p (pos_of p src sm) (PM.sr_rem src))
  /\ (PM.sm_st sm = 2 -> PM.sm_g sm = PM.sm_eg sm).      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition clink (p : list Z) (X : UbjRef.st) (s : PM.pst) (sm : PM.strm) (en : enc) (k : PESK.sink) : Prop :=
  PM.p_more s = b2z (s_more X) /\ PM.p_done s = b2z (s_done X) /\ PM.p_depth s = s_depth X
  /\ PM.p_stk s = stk_conv (s_stk X)
  /\ (s_more X = true -> s_done X = false -> pos_of p (PM.p_src s) sm = s_pos X)
  /\ en_stk en = rev (s_estk X) /\ en_depth en = s_edepth X
  /\ s_lo X <= PESK.sk_z k <= s_hi X
  /\ s_bad X = false.

(* [comment removed for export] *)
Definition ec_state (M : word -> option byte) (fb : Z) (e : bool) (cat : Z) : Prop :=
  if e then exists v, 1 <= v <= 64 /\ PMSP.ec_at segs M (PMSP.o_ec A fb) v (pa_errcat_obj A)
  else PMSP.ec_at segs M (PMSP.o_ec A fb) 0 cat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition owned (s : PM.pst) (en : enc) (k : PESK.sink) : list (Z * Z) := PM.parser_own s ++ enc_own en ++ PESK.sink_own k.
Lemma owned_app s en k LBX : PM.parser_own s ++ (enc_own en ++ PESK.sink_own k ++ LBX) = owned s en k ++ LBX.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCModel ()) ["WithImage"] "h03LBXh12enh21kh31lh41sp;2p;1p;3p;4p;6g00^hj2:Tg005=j19Tg00_Hj13Tg00`Xj15Tg00agj16Tg00Ubj30Tg009Oj31Tg008Ij28Tg00c7j42Tg000Mj64Tg00cUj37Tg00dbR0g00emR1g00g:R2g00>BR3/:3R3#9R4P4f3R5#3R6f2R7#5R8f1R9#6R:503R;f0R<503R=503f4#3R>%55%67=039503503R?=14<X34P4A03:<9038R@A03><914?X34A036@R@,84P=P3P8P:P<C2E4A036;=03<P3P6P;P<C2E4A7579=03<914@eX04X22X11X40P5P7P9P<O4W0W2W1W4o"). Qed.

Definition crun_pre (P : PESK.sink_policy) (M : word -> option byte) (fb : Z) (p : list Z) (X : UbjRef.st)
           (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : enc) (k : PESK.sink) (e : bool) (cat : Z) : Prop :=
  parser_at M (PMSP.o_p A fb) (PMSP.o_is A fb) s /\ iss_at M (PMSP.o_is A fb) str sm
  /\ enc_at M (PMSP.o_v A fb) fb en /\ L5.u64_at segs M (PMSP.o_p A fb + 384) (PMSP.o_v A fb)
  /\ sink_at P M (PESK.o_sink E fb) k
  /\ PMST.base_ok segs A M /\ PEST.err_ok segs A E M e /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
  /\ content_ok M fb p (PM.p_src s) str sm
  /\ clink p X s sm en k
  /\ ec_state M fb (s_ec X) cat
  /\ (s_ec X = true -> e = true).

(* [comment removed for export] *)
Definition W_crun (fb : Z) : list L5.range :=
  PMSP.W_run A fb ++ [(PMSP.o_v A fb, 56); (PESK.o_sink E fb, 24)].
(* [comment removed for export] *)
Definition W_enc (fb : Z) : list L5.range :=
  [(PMSP.o_v A fb, 56); (PESK.o_sink E fb, 24); (PMSP.o_ec A fb, 16)] ++ PMSP.err_W A.

Definition credit_add (c d : credit) : credit := (fst c + fst d, snd c + snd d).
Definition pot_all (P : PESK.sink_policy) (s : PM.pst) (en : enc) (k : PESK.sink) : credit :=
  credit_add (PM.pot_parser L s) (credit_add (pot_estack (en_k en)) (PESK.sink_pot P (PESK.sk_c k))).
Definition pot_enc (P : PESK.sink_policy) (en : enc) (k : PESK.sink) : credit :=
  credit_add (pot_estack (en_k en)) (PESK.sink_pot P (PESK.sk_c k)).

End WithImage.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ecap_nonneg k : 0 <= ecap k.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCModel ()) [] "p'0h07__arithh14__ffh28__varmaph35__with41kh51bi001bp;2p;1p;4p;3p;7g00hHj2FTg0035j1ETg004?j13Tg00hej21Tg00iBj2DTg00;:j20Tg004]j1;Tg005=j1:Tg005]j18Tg006;j17Tg006Yj16Tg007Dj22Tg00<1j44Tg007gj2CTg008Ij2BTg008cj2<Tg009Oj3=Tg009ij3>Tg00:Hj4?Tg00i_j3@Tg00jCj1ATg00<\j79Tf1R0g00>`g00??R1P1g00?_R1f0R2g00@fF9p=5g00>BR3g00=dR4,F2g00CeR5P5P5P3P2P4g00BTR6#E#3R7f2R8%36R6'1'Dn0100000020000,04P2g00C9R9#;R:%:9R9%83R;%73R<%63R=P31234R>g00@?R?P>C4'51C=1R1P2P8g00DER@,B51<28==5@dA>340C?R@b1b2b31044P2b01106P:P9P;P<P3P>P?1237C4,5=P1P@b1b2b31047P2b05@7n0110000020000b5%A2,04eX43P2O1W4o"). Qed.
Lemma ecap_step k : 1 <= k -> ecap (k + 1) = 2 * ecap k.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCModel ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51Hh61zh72Hah81bh91kh:1xh;1yh<2Hkh=6__sat0h>6__sat1p;1p;2p;3p;4p;6p;5p;7p;8g004?j1GTg00;:j28Tg00kOj24Tg00hHj26Tg00klj1ETg00lEj2XTg004]j1TTg005=j1NTg00lfj2LTg006;j1KTg006Yj1JTg007Dj2>Tg00mDj2]Tg00mgj1YTg00nIj3FTg007gj2WTg008Ij2VTg008cj2UTg009Oj37Tg009ij3STg00:Hj4QTg00nlj4ATg0035j1MTg00hej21Tg00iBj22Tg00oHj23Tg00oej3@Tg010Hj2OTg0110j2?Tg00i_j3PTg011Lj3BTg011oj1RTg001Fj6CTg005]j1_Tg012Pj5^Tg000Mj6=Tg00jCj1ITg00<1j4HTg00<\j7\Tg0133j6ZTg013Wj8[Tg00CeR0f0R1g014;R237p=:g00>BR3f1R4;71p=0P3P4g00@?P1CHp=<P4g00>`R5g00??R6P6g00?_R7P1g00@fF\p=5P3P4g014[P1CHp=9P4P5P6P6P7P1EZp=Df3R8P5P6P6P7f2R5P4P1G[p=;g00BTR9#GR:/81R;P0144:R<g00=dR='6R>P2g00;V1641#:1054#ER?[1041#E1654#:[R@1685#:\?1X41P1n2001000000120000000X;3X:3R?P@^;3^:3R@P1145:RAP=g00C9RB#TRC%NBRB1L34RD%K3RE%J3RF1>3:RG1]39RH'<,5FRI%Y6R6AF3HGRJ1>3=RK'9,5F,DFC;1WF7R7P1P5g00DERL,V01U15=70LdAS3=4CQRLb2b3b4X03A73<=g00SVRM[\;^03P1P8P5O2b1O3b5CAA702>P0P2P0P3P1P=%M9#GR9148:/1:R>'2n0100000020000P0P3168=RNP=118:RO,29n0100000020000,39'0X80P0165=R5P2P?P@P1P8P=PCPBPDPEPFPIP619HK,5F,DFC;P7PLb2b3b4X03A734=PM[\;^03P1f4RMP8O2b1O3b5CAA7025P0P214M:/1:R2,29P0P3P1P=11M:R5,29R8n0100000020000,39'0X80PCPBPDPEA@3HGR0=F3GA@3JG'9,5FP7PLb2b3b4X03111:/4:141:/1:'0^03P1PMO1b114O:/0>P3145:R>1291f5RO/1:RJ,29R@,39R?'0X63P3129:RP,38101?X63P3P913@1/0?X631O951?=918=Jf6/1:,29,?=[[18=9RJg00S:R?f7/1:R@=P94UW7129@R@,8=\?^7JPCPBPDPE1>39RJ9B3HAB3JH'9,5FP7PLb2b3b4X0313191391'0^03P1P@O1b1b=b>PP%R9EC129>P9P5P:PCPBPDPEPFPIP61<K0,5FC;P7PLb2b3b4X03114:,8=\;^03P1POPMO2b1PCPB%_3PE1<KG,5FP7PLb2b3b418=:P1b1D^ECP2P1E=b5PNP1E=b516A=P1E=b5%I<%I4,39'0eW<X93P1O1X93o"). Qed.
Lemma ecap_1 : ecap 1 = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCModel ()) [] "p;1p;2g004?j11Tg008Ij20Tg00>Bg00BT#1'0o"). Qed.

End PEC.
