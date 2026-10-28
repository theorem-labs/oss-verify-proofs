(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_ContStmt () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03c6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_ContStmt2lgK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subc6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_ContStmt5clossK46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3addc6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_ContStmt7lg_monoC56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission7LibCont9ContStmts5vgrowK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface4bptrC46Stdlib5Lists4List2hdc6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_ContStmt:closs_stepC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface3ICMI6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil8HeapCeil00".
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Record v4_consts : Type := V4C { v4_entry : Z; v4_del_ra : Z; v4_xmax : Z }.
Definition V32_SLOW_CREF : v4_consts := V4C 0xf871c 0xf8900 (2 ^ 32).
Definition V32_SLOW_RREF : v4_consts := V4C 0xf898c 0xf8b70 (2 ^ 32).
Definition VOT_SLOW_RREF : v4_consts := V4C 0xfb3d4 0xfb5bc (2 ^ 31).
Definition VOT_SLOW_CREF : v4_consts := V4C 0x100040 0x100228 (2 ^ 31).
Definition VOT_PB_ENTRY : Z := 0xf9260.
Definition VOPND_SLOW_ENTRY : Z := 0xfc400.
Definition VOPND_DEL_RA : Z := 0xfc600.
Definition MKSTR_ENTRY : Z := 0xea650.

Definition V4_STACK : Z := 112 + AOPNEW_STACK.
Definition VOT_PB_STACK : Z := 64 + V4_STACK.
Definition VOPND_STACK : Z := 96 + AOPNEW_STACK.

Definition v4_newcap (cap : Z) : Z := vgrow cap.

Definition lg (n : Z) : Z := if 64512 <? n then 8 * n else 0.
Definition closs (cap cap' : Z) : Z := lg (4 * cap') - lg (4 * cap).

Lemma lg_mono : forall a b, a <= b -> lg a <= lg b.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_ContStmt ()) [] "p'0h04__x1h12H0h27__arithh34__ffh48__varmaph55__with64__x2h72b0h82b1h91Hh:4__p1h;3Habh<1ah=1bi001bp;2p;1p;3p;4p;6p;7p;8g0000j20Tg000Lj15Tg0011j1ETg001Oj2GTg0021j22Tg002Mj28Tg002jR0j3?Tg003Nj1;Tg0043j21Tg004Pj2:Tg0059j1ATg005Xj3<Tg006Aj2FTg006mj2WTg007Yj1VTg0089j3DTg008Yj1UTg0099j2BTg009Wj1STg00:5j4RTg00:Sj1QTg00;1j1NTg00;\j2>Tg00<?j1MTg00<aj29Tg00=Dj3=Tg00=gj2LTg00>Ij2KTg00>cj2JTg00?Oj3OTg00?ij3ITg00@Hj4PTg00A:j4@Tg00Aej6HTg00BIj1CTg00CEj7TTg00Cij8XTf0R1#;#;p=4g00DMR2f1R3g00DkP1C@p=7P3g00ERR4g00F1R5P5g00FQR6P1g00G1FTp=3f3R7P4P5P5P6f2R8P3P1GXp=61031g00GQR9#5#5#5#5#5#4#4#4#4#4#ER:/G812:8108:18:83?18:7g00H6R;P0f4R<,2:10<:P;P2P3%;9R=#4#ER>f6R?'1g00HVR@n0100000020000P;P2f5RA,8:RB11>AP@n0100000020000'0P312:ARC1G:ARD10A:RE=?CBRC18:?R?P;P0f7RB,2:RF10B:RBf:RG,1>P;P2P3f9RH,1>P@n0100000020000RI'0P3f8RJ,2:RKg00I4RLg00I`RM,:2RN%AMRM#A,:2RO9<2Ng00J?RP'F'W%VLRQ3DRR%ULRSP21B28P3%S2RTCRRU%Q2RV%N2RW1>29R91>2=R='7,3WRX%M5RY192>RZ==29R[A=2Z='7,3WC61LW6RZP1P8g00JkR\,K;1J18=O;\dAI2@3CPR\b3b4b5X02X62101311>3R]11>8'0[^02^62P1PGf;R^PHO3b2W1P1O110J:RJp-0R_1:2M=<2N9<2O/FP=DLQPSPUPVPW192:RU,7=,3WPYPWP2PUg00KKP9C@,3WR9PYPWPXPYPWP4P5P5P6P<EHC6C6C6PZP\b3b4b5X02X62W:103:12:31087PA[[[^02^62^:_P111>^/0@PGP^P3PAPHO6b2W1P1O1n200210000000021000011000b8b7W9P1O1PDPCP?P;P0PFPB10@IP3PRPS1B23PVPWP9PY192@RY/7[,3WC6PZP\b3b4b5X0212:110@][^02P1PGP3O2b2X1KP1O1PQPSPTPV17YY,3WPZP\b3b4b510@@P1b2X1JP1O1n200210000000021000010000b8b7X9EP1O1n200210000000021100011000b8b7%C8%C3'0eW;X=2X<2o"). Qed.
Lemma closs_refl : forall c, closs c c = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_ContStmt ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51cp;1p;2p;3p;4p;7g007Yj1ETg008Yj1DTg0099j23Tg00:Sj12Tg00;1j1CTg00;\j2;Tg00L2j3:Tg00<aj24Tg00A:j45Tg00CEj76Tg00=gj27Tg00>Ij28Tg00>cj29Tg00?Oj30Tg00?ij3BTg00@Hj4=Tg00LUj2<Tg003Nj11Tg0011j1>Tg0043j2?Tg00BIj1@Tg00M2j2ATg00DMR0g00I4R1#E%D1f1R1,30%20%C0R2g00ERg00F1R3P3g00FQR3P0g00GQR4,;0R5=:05g00N1g00HVR5,40C5g00G1F61723f0R3f2R2g00H6R6g00JkR7'81932=067dAB051C=b2b3b4X001<33=005^00P3%14#1#>/?1#@O1b11A33=005eW5o"). Qed.
Lemma closs_tele : forall a b c, closs a b + closs b c = closs a c.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_ContStmt ()) [] "h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with71ah81bh91cp;1p;2p;4p;3p;7g007Yj1HTg008Yj1GTg0099j27Tg00:5j4=Tg00:Sj1FTg00;1j1BTg00;\j25Tg003Nj18Tg00L2j34Tg000Lj1>Tg00NXj3<Tg00A:j4;Tg00CEj7:Tg00=gj2ETg00>Ij2DTg00>cj2CTg00?Oj32Tg00?ij3ATg00@Hj4@Tg00LUj23Tg00O;j29Tg0011j1?Tg0043j20Tg00BIj11Tg00M2j26Tg00DMR0g00I4R1#H%G1P0f2R1,70f1R2f3R3,70C=%F0%B0R4g00ERg00F1R5P5g00FQR5P0g00GQR6,50R7%86R8,50R9540%>6,50R6=4075<0g00N1A4069C;g00G1F:1E45f0R5P1g00H6R4g00JkR6'D1C51=246dg00HV=A02C@b4b5b6X00X10X2013521315'91312520^00^10^20P5%88#?R8/02#11083#11081#1O3b316121625'91615520eX90X80W7o"). Qed.
Lemma closs_mono : forall c a b, a <= b -> closs c a <= closs c b.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_ContStmt ()) [] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with64__x3h71Hh83Habh91ah:1bh;1cp;2p;1p;3p;4p;7p;8g0000j20Tg003Nj1=Tg0011j1NTg0043j22Tg004Pj2?Tg0059j1;Tg005Xj3RTg006Aj2MTg006mj2ETg007Yj1DTg0089j3CTg008Yj1ATg0099j2<Tg009Wj1VTg00:5j4>Tg00:Sj1UTg00;1j1TTg00;\j25Tg00<?j1QTg00<aj2OTg00=Dj39Tg00=gj2LTg00>Ij2FTg00>cj2GTg00?Oj3HTg00?ij3ITg00@Hj4JTg00OXj3KTg00BIj11Tg000Lj1BTg00L2j36Tg00LUj28Tg00M2j2:Tg00A:j4PTg00CEj7@Tg00Cij8STg00DMR0f1R1g00Dkf0R2CPp=4P1g00ERR3g00F1R4P4g00FQR5P2g00G1F@p=3f3R6P3P4P4P5f2R3P1P2GSp=71012g00GQR7#=R8#=#NR9/23R:1291R;g00I4R<g00I`R=,?0R>%;=#;,?09R0>g00J?'M'E%D<R>3C%A<R<P01<03R=P1%V0C>%U0R?%T0R@1507RA1508R8'4,3@%Q4R41O09RB=90AA90B8'4,3@C71L@5R5P2P3g00H6RBg00JkRC'F1G23=HBCdg00HV=I01CJRCb3b4b5X00X10102110;:[^00^10P2P3P6P1O3b23K%1:%1;'0P>P<P0P=P11<06C>P?P@%B7,50R7,4A,3@P4A60A8A6078'4,3@C7P5PCb3b4b5X00X10X60102318131863'0[^00^10^60P21296#1f5,29#1f4,29#1P1O4b2b71:631:61'0eW8X:0X90X;0o"). Qed.

Lemma closs_step : forall c, 0 <= c -> (if 4 * vgrow c <=? 64512 then 0 else 4 * (4 * vgrow c)) <= closs c (vgrow c).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_ContStmt ()) [] "p'0h04__x1h12H1h27__arithh34__p1h42H2h51bi001bh62b0h72z2h84__ffh98__varmaph:5__with;2H0h<4__p2h=4__x2h>1Hh?4__p3h@2HchA1cp%0p;1p;2p;3p;4p;7p;6p;8g003Nj1BTg0011j1?Tg0043j20Tg00O;j2<Tg000Lj1=Tg00PYj2`Tg0000j21Tg0021j22Tg00Q;j2MTg002jR0j3LTg002Mj2DTg00LUj25Tg001Oj2VTg00QXj2GTg00R5j2hTg00?Oj39Tg00RWj2;Tg00S2j2NTg007Yj1bTg008Yj1aTg0099j2STg00:Sj1_Tg00;1j1^Tg00<aj2:Tg00;\j2RTg00<?j1]Tg00=gj2\Tg00>Ij2[Tg00>cj2ZTg00?ij3sTg00@Hj4rTg0059j1QTg004Pj2PTg00SLj2qTg00T5j3pTg00T^j1YTg00U<j2XTg00U]j3WTg005Xj3@Tg006Aj2KTg006mj2>Tg0089j3JTg009Wj1lTg00:5j4kTg00NXj3UTg00A:j4ITg00L2j3OTg00VFj1gTg00M2j2fTg00=Dj3iTg00CEj7jTg00Aej6eTg00Cij8nTg00WBj7oTg00Wfj7cTg00HVR1f0R2'1p=7f2R3f1R4/G2'0p=m%B2#Bp=Af4R5f3R6/031<42'G'0p=61034/G2p=dg00DMR7?i42p=8P7P4g00KKP2CIp=FP4g00ERR8g00F1R9P9g00FQR:P2g00G1Fjp=3P7P4g00DkP2CIp=CP4P8P9P9P:P2Eep=EP6P8P9P9P:P3P4P2Gnp=4P3P8P9P9P:P4P2Fop=HP3P8P9P9P:P4P2Fcp=T%72g00GQR8#BR;#BR<#?R=%?;R>/04R?%?8R@,<4RA3mRB%=8#=#=#=#=#A#A#A#A#A#?RC'`11BC12CB1MBC3LP=P>P3P3P@D6/MCg00H6RBP0P=P>P6P6P@D6RD/1C12CDPBP7P4P1P=P>f5RDPDP@D6RE,0=n0100000020000PBP71DCERF%B<#?RG/0EP1n0100000020000PBP710=DRH,DC10GHP1n0100000020000'5'1P4P=P>P5P5P@D6RH/1C1VCERI12CE11EC;LFRFP=P>f6REPEP@D6,DCRJPBP0P=P>f7RKPKP@D6RL,2CRM11LCRLPBP7P4P=P>f9RNPNP@D6RO,0GP1n0100000020000PBP710=NRN,DCRP10GNP1n0100000020000'5RQ#7P4P=P>f8RRPRP@D6RR,2CRS1VCNRT12CN11NC;LPRPf:,0=,DCRNPBP0f;RU,0=RV,2CRW11VCRVf=RX,0>RY1<X@RZ'GR[,0=R\,0GPBP7P410=X,0GP1n0100000020000RX'5R]#7P4f<,0=R^,2CR_1hYZR`12YZA97[Z';11ZYA97[Y';'NR[f>RY1<Y@5d>RYP7p-0RZg00I4Ra#bRb%aaRc1S74Rd%_7Re%^7Rf1:7CRg1:7=Rh1R78Ri'8Rj'F,3fRk%]9R9Pf1Cjg,3fS00P91Ef6S01C4C41\f:R:P2P3g00JkRl,[B1Z23=9BldAs714CrRlb8b9b:X07W3Rm10=2Rn,2CRo10=4Rp/1CP6[[^07^3ZRqP210GpRrf@Rs,0=,0GRt'5#7P4PKPUO4b2b7b4W1P2O111^CR^P`P[PYP7PmPqP215r1Rr#7P4PKPUO4b2b7b4W1P2O1n200210000000021100011000b6b5W;P2O111RCRRPTPPPNPBP0PWPV151XRX#7P4P`P[PYP7g00I`Rq#QRm,P7Ru1q7G1P7qRq5p7%Y<,X7%Qm#Q,P7Rm5W7=@7u5@7g00J?R<'K'>A@7qm/K<,>u=JabRv5JaPcP71S73P4%l7RwCkRxPePf1:7>Ry/8iRz1:7@R{9U7i'F,3f1Ef5R55Hf1EfDRDP71R7;R;g00N1R|PzCI,3f5Hf5TfP9PfPkP9Pf18h;Rz/Cg,3fP91EfEC4C4C4P:Plb8b9b:X07X=7X3ZX<ZX?Z10>2RE1<2@'2/;3A974E,;6'N12CpRE10=6R}/1CPK[[[^07^=7^3Z^<Z^?ZP2151tRt#71<s@R@10>s'1R>A974@R@P4PsP3P6PKO8b2b7b4X1_P2O1PbPcPwPe1:71RwAO7ww'C,3fP:Plb8b9b:1511R~#7P2b2X1^P2O1n200210000000021100010000b6b5W;P2O1n200210000000021100011000b6b5W>P2O112CHPIPFPJPBP0PMPL10=O/1QP4PTPPPNPBP0PWPV10=\R\/1]P4P`P[PYP7%Y8,X7=W7m9@7q/K<,>q=JavPcPxPePf18y;RyAU7;{'F,3f=Hf5P7PiP|PyCI,3f9HfD5TfP9Pf1Fgz,3fP918hjRh1:7GRg/8jRj18gz5O7'C,3fC4C4P:Plb8b9b:X07X=7X3ZX<Z12?A/;3A972?,;6'N10=3R?,2C10=?10G?10G}'5'1[[^07^=7^3Z^<ZP2P>P@PsP4P3P6O6b2b7b4X1_P2O1P`P[PYP7A@7uq/K<,>u,>u=JabPcPdPePfPkP9AO7jw,Ch,3fC4P:Plb8b9b:X0710=pRp/1r\o^07P2P4PKO2b2b7b4X1^P2O1n200210000000021100011000b6b5X;SP2O1PTPPPNPBP0PWPV11\XP4P`P[PYP7PbPcPdPePfQ00P9PfPkP9Q01C4C4P:Plb8b9b:X07X3ZRl11nCP6\E[^07^3ZRZP211ptP4PKPUO4b2b7b4X1_P2O1P`P[PYP7PlPZP211p~P4PKPUO4b2b7b4X1^P2O1n200210000000021100011000b6b5X;RP2O1n200210000000021100011000b6b5W>P2O1n200210000000021100011000b6b5PBP7%g4RB,0=R2/MCP110=2n01000000200001f4B'1eW@XA7o"). Qed.
Lemma closs_step_ICM {HCEIL : HeapCeil} : forall c, 0 <= c -> ICM (4 * vgrow c) <= closs c (vgrow c).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_ContStmt ()) [] "h05HCEILh12Hch21cp;2p;1p100XJp4p70p100YBp4p710p8g0000j21Tg00YYj27Tg003Nj10Tg0011j12Tg00VFj16Tg0043j25Tg00Z]j14Tg00M2j23Tg00[VR0g00DMg00HVf0R1'1f1R2/71g00GQ#0#0#2%62R3'5#41323'1eW1W2X00P1O1W0o"). Qed.

Definition vec32A (LB : list block) (m : mem) (v b : Z) (xs : list Z) (cap : Z) : Prop := @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m v b xs cap.
Definition vopndA (LB : list block) (m : mem) (v b n cap : Z) : Prop := @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m v b n cap.
Definition fldA (m : mem) (a : Z) (k : nat) (x : Z) : Prop := fld ASEGS m a k x.

Section ContA.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition obj_win (LB : list block) (LF : list fframe) (spz lo a n : Z) : Prop :=
    aclient_range H LB spz a n /\ aclient_range H LB spz (sh a) (nsh n)
    /\ aclient_write_ok H LB (a, a + n) /\ afs_write_ok H LF (a, a + n) /\ aconst_ok (a, a + n)
    /\ (a + n <= lo \/ spz <= a).

  Definition src4_keep (LB : list block) (spz : Z) (m : mem) (src x : Z) : Prop :=
    forall m', ACONST m' -> mem_inv asegs m' -> apres H LB spz m m' -> fldA m' src 4 x /\ accessible m' src 4.

  Definition src4_keep_x (LB : list block) (spz : Z) (X : list (Z * Z)) (m : mem) (src x : Z) : Prop :=
    forall m', ACONST m' -> mem_inv asegs m' -> xpres H LB spz X m m' -> fldA m' src 4 x /\ accessible m' src 4.
  Definition srcb_keep (LB : list block) (spz : Z) (m : mem) (src : Z) (bs : list byte) : Prop :=
    forall m', ACONST m' -> mem_inv asegs m' -> apres H LB spz m m' ->
      bytes_at asegs m' src bs /\ accessible m' src (Z.of_nat (length bs)) /\ shvis m' src (src + Z.of_nat (length bs)).

  Definition v4_oldblk (LB : list block) (b cap : Z) (pid : bptr) : Prop :=
    (b = 0 /\ cap = 0) \/ (0 < cap /\ In (pid, b, 4 * cap) LB).

  Definition v4_oldx (b n : Z) : list (Z * Z) := if b =? 0 then [] else [(b, b + n); (sh b, sh b + nsh n)].

  Definition v4_newLB (LB : list block) (b : Z) (pid pid' : bptr) (b' n' : Z) : list block :=
    (pid', b', n') :: (if b =? 0 then LB else as_lb_remove H pid LB).

  Definition v4slow_post (c : v4_consts) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (v b cap x : Z) (xs : list Z) (pid : bptr) (lo B shi : Z)
      (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (pid' : bptr) (b' : Z),
      let cap' := v4_newcap cap in

      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (b' + 4 * (cap + 1))) a1 a2 a3 a4 a5 a6 a7
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B

      /\ xpres H LB (bv_unsigned sp) ((v, v + 24) :: v4_oldx b (4 * cap)) m m'
      /\ ablock_range H b' (4 * cap') /\ as_RHEAP H s' (v4_newLB LB b pid pid' b' (4 * cap')) m'
      /\ vec32A (v4_newLB LB b pid pid' b' (4 * cap')) m' v b' (xs ++ [x]) cap'
      /\ SHAD m' b' (cc_gen (4 * cap') (4 * (cap + 1)))
      /\ addressable m' v 24

      /\ wr_at asegs m' v 24 /\ lb_own (v4_newLB LB b pid pid' b' (4 * cap')) m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - (as_Cm H (4 * cap') + as_Cf H (4 * cap)).

  Definition v4slow_stmt (c : v4_consts) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (v b cap src x : Z) (xs : list Z) (pid : bptr)
           (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (v4_entry c)) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 v -> a1 = Z_to_bv 64 src ->

      vec32A LB m v b xs cap -> Zlen xs = cap -> v mod 8 = 0 ->
      addressable m v 24 -> obj_win LB LF (bv_unsigned sp) lo v 24 ->
      ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)) ->
      wr_at asegs m v 24 -> lb_own LB m ->
      v4_oldblk LB b cap pid -> (0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * cap))) ->
      4 * v4_newcap cap <= 2 ^ 26 ->

      src4_keep LB (bv_unsigned sp) m src x -> 0 <= x < v4_xmax c -> src mod 4 = 0 -> 0 <= src -> src + 4 <= 2 ^ 47 ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> as_alloc_ok H s LB (4 * v4_newcap cap) ->
      as_Cm H (4 * v4_newcap cap) + as_Cf H (4 * cap) <= as_AL H s ->
      trace_ok (as_TR H) APC0_FREE [v4_del_ra c] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->

      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - V4_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_SR H (v4slow_post c ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap x xs pid lo B shi m mo)
        (mkCfg msF mo).

  Definition votpb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (v b cap x : Z) (xs : list Z) (pid : bptr) (lo B shi : Z)
      (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block) (b' cap' : Z),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ vec32A LB' m' v b' (xs ++ [x]) cap' /\ as_RHEAP H s' LB' m'
      /\ SHAD m' b' (cc_gen (4 * cap') (4 * (Zlen xs + 1)))
      /\ addressable m' v 24 /\ wr_at asegs m' v 24 /\ lb_own LB' m'
      /\ ((Zlen xs < cap /\ b' = b /\ cap' = cap /\ LB' = LB
           /\ xpres H LB (bv_unsigned sp) [(v, v + 24); (b, b + 4 * cap); (sh b, sh b + nsh (4 * cap))] m m'
           /\ as_AL H s' >= as_AL H s)
          \/ (Zlen xs = cap /\ cap' = v4_newcap cap
              /\ (exists pid', LB' = v4_newLB LB b pid pid' b' (4 * cap') /\ ablock_range H b' (4 * cap'))
              /\ xpres H LB (bv_unsigned sp) ((v, v + 24) :: v4_oldx b (4 * cap)) m m'
              /\ as_AL H s' >= as_AL H s - (as_Cm H (4 * cap') + as_Cf H (4 * cap))))
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

  Definition votpb_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (v b cap src x : Z) (xs : list Z) (pid : bptr)
           (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 VOT_PB_ENTRY) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 v -> a1 = Z_to_bv 64 src ->
      vec32A LB m v b xs cap -> v mod 8 = 0 ->
      addressable m v 24 -> obj_win LB LF (bv_unsigned sp) lo v 24 ->
      ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)) ->
      wr_at asegs m v 24 -> lb_own LB m ->
      v4_oldblk LB b cap pid -> (0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * Zlen xs))) ->
      4 * cap <= 2 ^ 26 -> (Zlen xs = cap -> 4 * v4_newcap cap <= 2 ^ 26) ->

      src4_keep_x LB (bv_unsigned sp) (if b =? 0 then [] else [(sh b, sh b + nsh (4 * cap))]) m src x ->
      0 <= x < 2 ^ 31 -> src mod 4 = 0 -> 0 <= src -> src + 4 <= 2 ^ 47 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      (Zlen xs = cap -> as_alloc_ok H s LB (4 * v4_newcap cap)
                        /\ as_Cm H (4 * v4_newcap cap) + as_Cf H (4 * cap) <= as_AL H s) ->
      trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - VOT_PB_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_SR H (votpb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap x xs pid lo B shi m mo)
        (mkCfg msF mo).

  Definition vopnd_slow_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (v b cap : Z) (pid : bptr) (lo B shi : Z)
      (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (pid' : bptr) (b' : Z),
      let cap' := v4_newcap cap in

      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (b' + OPND_SZ * (cap + 1))) a1 a2 a3 a4 a5 a6 a7
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) ((v, v + 24) :: v4_oldx b (OPND_SZ * cap)) m m'
      /\ ablock_range H b' (OPND_SZ * cap') /\ as_RHEAP H s' (v4_newLB LB b pid pid' b' (OPND_SZ * cap')) m'
      /\ vopndA (v4_newLB LB b pid pid' b' (OPND_SZ * cap')) m' v b' (cap + 1) cap'

      /\ SHAD m' b' (cc_gen (OPND_SZ * cap') (OPND_SZ * (cap + 1)))
      /\ addressable m' v 24 /\ wr_at asegs m' v 24 /\ lb_own (v4_newLB LB b pid pid' b' (OPND_SZ * cap')) m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - (as_Cm H (OPND_SZ * cap') + as_Cf H (OPND_SZ * cap)).

  Definition vopnd_slow_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (v b cap src : Z) (bs : list byte) (pid : bptr)
           (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 VOPND_SLOW_ENTRY) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 v -> a1 = Z_to_bv 64 src ->
      vopndA LB m v b cap cap -> v mod 8 = 0 ->
      addressable m v 24 -> obj_win LB LF (bv_unsigned sp) lo v 24 ->
      ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)) ->
      wr_at asegs m v 24 -> lb_own LB m ->
      ((b = 0 /\ cap = 0) \/ (0 < cap /\ In (pid, b, OPND_SZ * cap) LB)) ->
      (0 < cap -> SHAD m b (cc_gen (OPND_SZ * cap) (OPND_SZ * cap))) ->
      OPND_SZ * v4_newcap cap <= 2 ^ 26 ->

      srcb_keep LB (bv_unsigned sp) m src bs -> Z.of_nat (length bs) = OPND_SZ ->
      in_app_mem src (src + OPND_SZ) -> (src + OPND_SZ <= lo \/ bv_unsigned sp <= src) ->
      (aclient_range H LB (bv_unsigned sp) src OPND_SZ \/ src + OPND_SZ <= AIMG_TOP) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> as_alloc_ok H s LB (OPND_SZ * v4_newcap cap) ->
      as_Cm H (OPND_SZ * v4_newcap cap) + as_Cf H (OPND_SZ * cap) <= as_AL H s ->
      trace_ok (as_TR H) APC0_FREE [VOPND_DEL_RA] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - VOPND_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_SR H (vopnd_slow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap pid lo B shi m mo)
        (mkCfg msF mo).

End ContA.
