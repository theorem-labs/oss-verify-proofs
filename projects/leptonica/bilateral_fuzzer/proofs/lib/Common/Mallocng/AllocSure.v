(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg AllocIface PureModel AsanCeil VmLedger.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_AllocSure () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05c69OSSVerify5KrLib6Common8Mallocng9AllocSure<alloc_marginC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition alloc_margin (n : Z) : Z :=
  if n <=? 2028 then Z.min (2^17) (n + 2^22) else Z.min (n + 2^20 + 2^16) (52 * n + 2^16 + 2^12).

Lemma alloc_margin_le : forall n, alloc_margin n <= n + 2^22.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSure ()) [] "p'0h02Hah14__p1h24__x1h34__x2h42H0h57__arithh64__ffh76__sat1h86__sat2h96__sat3h:6__sat4h;8__varmaph<5__with=2z0h>6__sat5h?6__sat6h@6__sat7hA6__sat8hB1bi001bhC1np;1p;2p;3p;4p;6p;7p;8g0000j12Tg000Uj11Tg001:j14Tg001Xj2RTg0025j2<Tg002Rj20Tg002oj2DTg003Lj2FTg003ij27Tg004Ej2KTg004gj2@Tg005Cj2BTg005]j2>Tg006Ej3:Tg006ij1HTg007Hj2ETg0081j3GTg008Zj2NTg009Fj1YTg009fj3MTg00:Fj1XTg00:fj2WTg00;Dj1VTg00;bj4UTg00<@j1TTg00<^j1STg00=Ij2JTg00=lj19Tg00>Jj3=Tg00>mj2ITg00?Pj3;Tg00@3j4?Tg00@^j6QTg00ABj1iTg00Adj2hTg00BFj2gTg00B`j2fTg00CLj3OTg00Cfj3cTg00DEj4bTg00E7j2_Tg00E`j3]Tg00FIj2\Tg00G5j3^Tg00GXj1[Tg00Hcj2`Tg00I>j7aTg00Ibj7ZTg00JFj7dTg00Jjj8eTf2R0g00KNR1f1R2f0R33O'`p=5g00KlR4/@3p=81743p=3P2g00LJR5g00LiR6P6g00MIR7P3g00MiFap=6P1P2g00NIP3C?p=CP0P5P6P6P7P2P3FZp=AP0P5P6P6P7P2P3Fdp=Lf3P5P6P6P7P0P2P3Gep=Pg00O0R8#2R9#2#2#2#2#1#2#2#1#1#4,R3g00OUR:P:P:P1P3%18R;#4R<%1;#1R=#2R>#4R?'<R@%2;RA#2#1RB#4RC,<<RD,00RE'DRF%1A#1RA#4RG,<<RH,00%1=R=#4RI,<<RJ'0%19R9#2#1#1#4RK/F0/0J%19R9#4RL,<<RM'0'DRNn0100000020000/7EP3102DRO,K@1@@ORP1D@ORQ;5@17O@?5QO'BPFP11><?%8<RF%3?%8@[[%3<RQg00P5RRA:<?2UW0%3@\R^0Q1><CR?%3C%8D[\FRSA:<C2VRX0QRC%3D\R^0QRTp-0RUg00PQRVg00Q=RW#HRX#HRY,E11E1X1E1WRW5G1RX5G1g00Q\RZ'N%YVR[3M%XVR\P11W10P2%V1CUR]%T1R^%S1R_P11J1<R`%9>5=1R>g00RH1I1;R;%9B9=1`5;1RBC?,6_1I18R8/C>,6_5A_P_P5P6P6P7f4EQR51C8B,6_5A_5L_%i6R6P1P8g00RoR>PBC?,6_RBCP1h_7R7P3P0g00SVRa,g:1f30=O:adAc142CbR4b6b;b<X21X31W1A5P3@A503O'B172ERE[^21^31^1UP3f8RO/0D/7@POf5f6O4b5b7b8b9b:b=b4102H/0JRO1FK2/0J/0MR@'K1@O@1DO@RP;5O17@ORa?5P@'BPNP11><L%3L%8M[\FA:<L2VRX0Q%3M\R^0Q1><G%3G%8H[\FA:<G2VRX0Q%3H\R^0QP?PSPCPT1><I%3I%8J[\FA:<I2VRX0Q%3J\R^0Q%29#2#4,_1=]1W%HY,E15G1/NZ,\X=MV[P\P]P^P_%9A9=1`9;1;%9=9=1`R=5;1RA,C8,6_9A_5P11J1K=^1;=;1=%999=1`5;1R`P>PAC?,6_1C8`,6_5A_5L_P6PBCPP7P4b6b;b<X21X31X1UA503OA5a3@'BPE[^21^31^1UP3f<RU/0H/0J1FKU/0J/0M'@PUf9f:O4b5b7b8b9b:b>b?b@bAb=b4n0110000020101bB%[3103D'7eXC1o"). Qed.
Lemma alloc_margin_ge : forall n, 0 <= n -> n <= alloc_margin n.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSure ()) [] "p'0h02Hah14__p1h24__p2h34__x1h44__x2h51Hh62H0h77__arithh84__ffh96__sat1h:6__sat2h;6__sat3h<6__sat4h=8__varmaph>5__with?2z0h@2HnhA6__sat5hB6__sat6hC1bi001bhD2b0hE1np;1p;2p;3p;4p;6p;7p;8g0000j13Tg000Uj10Tg001:j18Tg00T6j2oTg003ij22Tg004gj27Tg001Xj2STg00TXR0j3^Tg0025j2>Tg002Rj2;Tg002oj2CTg003Lj2ETg004Ej2VTg00Hcj24Tg005Cj2GTg005]j2?Tg006Ej3@Tg00U<j1`Tg00UZj2_Tg006ij1MTg007Hj2LTg00V;j3RTg0081j3DTg008Zj2KTg009Fj1]Tg009fj3JTg00:Fj1\Tg00:fj2[Tg00;Dj1ZTg00;bj4YTg00<@j1XTg00<^j1WTg00>mj2PTg00=Ij2HTg00=lj1BTg00>Jj3<Tg00?Pj3=Tg00ABj1nTg00Adj2mTg00BFj2lTg00B`j2kTg00CLj3TTg00Cfj3gTg00DEj4fTg00FIj2eTg00G5j3dTg00@3j4NTg00GXj1cTg00@^j6bTg00I>j7hTg00Ibj7aTg00JFj7iTg00Jjj8jTg00KlR1f0R2'2p=1f2R3f1R4';/;2p=9g00KNR5?T42p=61712p=:P4g00LJR6g00LiR7P7g00MIR8P2Ebp=QP5P4g00NIP2CNp=OP4P6P7P7P8P2g00MiFhp=5P3P6P7P7P8P4P2Fap=IP5P4g00RoP2CNp=FP3P6P7P7P8P4P2Fip=Uf3R9P6P7P7P8P3P4P2Gjp=A%12g00O0R6#3R:#3#3#3#3#0#3#3#0#0#8R;,o4124;R<17;4R=1S4;3^1S3;g00OUR>P0129;17;9f5R0P>P5P4%06R?#8R@%0?#0RA#3RB#8RC'>RD%3?RE#3#0RF#8RG,>@RH,;0RI'CRJ%0E#0RE#8RK,>@RL%0ARA#8RM,>@RN590RO%0:R:#3#0#0#8RP/E0%0:R:#8RQ,>@RR79NRS'CRTn0100000020000'2P4f4RU/2;1VDI17DI16JD'412ID16JI'4'Gf6RJ/;H,CDP51?@C%:@RI%1C%:D[[%1@RVg00P5RWA@@C4UW0%1D\W^0V1?@G%1G%:H[\IA@@G4VWX0V%1H\W^0Vp-0RGg00PQRC%`6,_5RXg00Q=RY#M#MRZ#M,L55R51L5ZRZ1L5YRY5D55D5g00Q\R['K%]CR\3J%\CR]P51[53P4%Z5CYR^%X5R_%W5R`1Q`URa1P5?R?1H5@Rb%BB5<5RB'O,5`5I`1P56R6%BF9<5b5=5/FB,5`1Q`0RB5I`5U`%n7R7P`1H5;RF,F6,5`P7P`1H51/F6,5`P71F6?,5`RcCACACA1m`8R8P2P3g00SVRd,l>1k23=T>ddAg514CfR1b8b=b>X35X45X1GW2164D,431;2H/2D/49'G%13129U[\<[^35^45^1G^2GP2f<R</;HRH,6017DHP0P<PJf7R<f;O7b7b9b:b;b<b?b6W5P2O117;U1VOS17OS16TO'412SO16TS'4'GA9JLN1EPJ?9NR'CP51?@Q%1Q%:R[\IA@@Q4VWX0V%1R\W^0V1?@K%1K%:L[\IA@@K4VWX0V%1L\W^0V1?@M%1M%:N[\IA@@M4VWX0V%1N\W^0VAR5XZ=D5YRXAD5YZ/K['e1KX[=JC\5JCP]P^P_P`%BE9<5b9=56%BA9<5bRA5=5,O?,5`9I`a1H5P=d56==5A%B:9<5b5=5,O?,5`9I`B5U`P7P`P5PFg00RHP6CN,5`P7PcCACAP8P1b8b=b>X35X45X1GX2GA92LN,64,431EP2?9NR,64,49'G1239\=[^35^45^1G^2GP2f>RG,EP?9NRRRA9GLNRN'217NRP<PGf8f9O6b7b9b:b;b<bAbBb?b6W5P2O1n200210000000021100011000bDbC%c4,24eW@XE5o"). Qed.
Lemma alloc_margin_mono : forall n n', n <= n' -> alloc_margin n <= alloc_margin n'.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSure ()) [] "p'0h02Hah14__p1h24__x1h34__x2h44__x3h54__x4h64__p2h72H1h82H2h92H3h:7__arithh;4__ffh<6__sat4h=6__sat5h>6__sat6h?6__sat7h@8__varmaphA5__withB2z2hC2z3hD6__sat8hE6__sat9hF1bi001bhG2b0hH2H0hI7__sat10hJ7__sat11hK7__sat12hL7__sat13hM1HhN1nhO2n'p%0p&0p;2p;1p;3p;4p;7p;6p;8g003ij20Tg0000j14Tg000Uj13Tg001:j1>Tg00T6j2nTg004gj22Tg001Xj2WTg00TXR0j3fTg0025j2PTg002Rj28Tg002oj2TTg003Lj2ATg004Ej2XTg005]j2OTg006Ej3MTg006ij1ETg00U<j1lTg00UZj2kTg00V;j3ZTg007Hj2bTg009Fj1rTg00:Fj1qTg00:fj2`Tg00;Dj1pTg00;bj4_Tg00<@j1oTg00<^k100Tg00=Ij2]Tg00=lj1STg00>Jj3RTg00>mj2YTg00ABj1~Tg00Adj2}Tg00BFj2|Tg00B`j2{Tg00CLj3[Tg00Cfj3yTg00DEj4xTg00E7j2jTg00FIj2NTg00G5j3iTg00Hcj2KTg00GXj1hTg005Cj2gTg0081j3VTg008Zj2cTg009fj3dTg00?Pj3wTg00@3j4\Tg00I>j7eTg00Ibj7vTg00JFj7uTg00@^j6tTg00Jjj8zTg00E`j3sTf2R1f1R2f0R3'8'Tp=?1812/83p=11A12/83p=Ug00KNR4?[23p=:A[423,K1p=C1K12/g3p==g00KlR5/23p=I1053p=71b43p=JAV4239V41p=FAV423p=Gg00Q\R6,c3p=aAV423/c6p=;g00PQR6Ad6237d1p=DAw423p=9P4P2g00RHP3C\p=LP2g00LJR7g00LiR8P8g00MIR9P3g00MiR:Fep=<P1P7P8P8P9P4P2g00NIP3C\P:Fep=@P1P7P8P8P9P2P3Fvp=5P4P2g00RoP3C\p=QP1P7P8P8P9P2P3Fup=BP2P7P8P8P9P3Etp=mf3R:P7P8P8P9P1P2P3Gzp=6As423p=H1K23,g1p=^1023g00O0R7#4R;#4#4#4#4#3#4#4#3#3#>R<,n1101<12<11W1<3f1W:<g00OUR=P0f4R>/0<S0012<>S01P=P4P2%37R?#>R@%3?RA#3RB#4RC#>RD'PREf6RF%4?RG#4#3RH#>RI,P@RJ3?%3G#3RG#>RK,P@RL%3BRB#>RM,P@RN51F%3;RO#4#3#3#>RP?UFN%3ORO#>RQ,P@RR3?n0100000020000P=P4f5RS/W<RTA?ESJA1SLNAUPSN;?Rn0100000020000'0P210S<RU1nS<S0212<SRV=fUTS031WF<S04P=P0f7RU/0<S0512<US06f:RT=?EJS07P=P4P2f9RW/8JRX,TERYA1WLNRZ1APW?1NRR['TR\n0100000020000S08'0P2f8R]/0<S091XEXS0:12EX1:YE10XE?CYX3=S0;Q07P4f<RY/8JRX,XER^12EX1TEXR_/:E10XE?C_X3=R_f=RX=?EJR`P41O@DS0<%I@Ra%7D%IE[[Rb%7@Rcg00P5RdAM@D2UW0RD%7E\d^0cRe1O@IRf%7I%IJ[\aRgAM@I2VdX0cRI%7J\d^0cRhp-0Rig00Q=Rj#ERk#ERl#ERm#JRn%l7,k4Ro%JlRl5Z4Rp%JkRk1b4jRj3FS0='GRq#a%EmRm#JRrAFnpjRs';%as1;rq%r6Rq3D3D%q6R6P4P41`4>P1%p4C_P21`4:C_Rt%o4Ru&004Rv1]4@Rw%SC5R4RC1Y4;R;%SH9R4wRH'9Rx'L,<v1Y47R7=@vCRy55v1QxC,<vA@v7x55vRx5Bv%~8R8Pv1mvFRz1Y4?R?=@vC55v1mvURC1Y4ARA/9H9@v?55v5BvP8Pv1Q;A,<vP81Q7?,<vS0>C6S0?C6C61}v9R9P3P1g00SVRH,|=1{31=[=HdAy452CxR5b;b@bAX24X34X44X54X1iW6181JRH,2E1:3ER{10HE?C3HRH3=1:1E18>J9CF15=S10>SS0@10:>R:[S0A[[^24^34^44^54^1i^6iP3fBR|/8JR}/0E12E}P|fCS0BPUPSPFP]fAO9b:b<b=b>b?bCb9bBb8W7P3O112<]R|1XZ[S0C12Z[1:\Z10[Z?C\[3=S0DA1TLNAUPTN;?RR\P4P^P_P`P41O@QR`%7Q%IR[\aR_AM@Q2VdX0cRQ%7R\d^0cR^Q0<PbPDPe1O@KR[%7K%IL[\aRZAM@K2VdX0cRK%7L\d^0cR}PfPgPIPh1O@MR~%7M%IN[\aRaAM@M2VdX0cRM%7N\d^0cRc1j4PRd/Hk/Gj9Fnp,;r%EmRm#E#JRp%JmRmAZ4onRo;FkR@'G,;j,Nn1;j@,Nn1;jl,NsRs;Dq3DP6PtPuPvA5vzy=BvxP8Pv%SG9R4wRG,9A%SB9R4wRB'9Rx1]4PRy=i4A/9B%SO9R4wRw'9R@'L,<vA@v?x55vRxA@v?@R@95vC5BvP8Pv1]4<R</LA,<vP8Q0>C6C6C6P9P5b;b@bAX24X34X44X54X1iX6iA=>{HA1>LNRH1AP>?1NRR{'2?C1HRH1:1{R{7^FP:\V[[^24^34^44^54^1i^6iP3fHR:,AP?1NRA1:LN'0fIR?/8J,2EP:P?PXf;REPYf>f?S0>O9b:b<b=b>b?bDbEbIbJbKbLbCb9bBb8W7P3O1n200210000000021100011000bGbFWHP3O1Q02Q03Q04P=P0Q05Q06Q08,0\P2Q09Q0:Q0;Q07P4A1YLNR01APY?1NRR='XS07120=1T0=RJ/:010=0?CJ=3=RJA1XLNAUPXN;?RR=P4P`P_PQP^P[PZPKP}Q0<PbPDPeP~PaPMPcPfPgPIPh1Glk,;nRh?DhqP6PtPuPv19;G/9BRGAi4y;/9B/9wRw'L,<vRB=5vzA@v7wRy95vC5BvP8Pv1QA<,<vP8Pv1L<;,<vP8Q0?C6C6C6P9P5b;b@bAX24X34X44X54X1iX6iA11LNR<1AP1?1NRR;'2RA1:3;RC,KS7=>Q00Q0110SFQ0@[[[[^24^34^44^54^1i^6iP31AP??1NRA1?LNRF'01:EFP:P?PXPEPYQ0>Q0BfGO:b:b<b=b>b?bDbEbIbJbKbLbCb9bBb8W7P3O1Q0CQ0DP\P4Q07PJP=P4P`P_PQP^P[PZPKP}P~PaPMPc%4O#4RO#>,j4Rc/HjRj1Hdp1Hcm%lO,k4=Z4n1Hck'G3F';,NnQ0=,;r1Hdl/Gk9Fro,;j,Nr;Dq5DsP6PtPuPvA@v7G95vB1QwG,<v=5vy5BvP8PvA5vz@9BvxP8Q0?C6C6P9P5b;b@bAX24X34X44X54X1i1:3<10;</KC5=AA^HS{Q0A[[^24^34^44^54^1iP3fDRi,AP?1NRA1iLN'0PifEPWPUP]PTQ0BO8b:b<b=b>b?bDbEbCb9bBb8X7|P3O1n200210000000021100011000bGbFXHVP3O1n200210000001021100011000bGbF%h1%h2'0eWMXO4XN4o"). Qed.
(* [comment removed for export] *)
Lemma alloc_margin_small : forall n, 0 <= n <= 2028 -> alloc_margin n = 2^17.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSure ()) [] "p'0h02Hah14__p1h24__p2h34__x1h41Hh52H0h67__arithh74__ffh84__p3h96__sat1h:6__sat2h;6__sat3h<6__sat4h=8__varmaph>5__with?4__x2h@2z0hA2HnhB6__sat5hC6__sat6hD6__sat7hE6__sat8hF1bi001bhG2b0hH1np;1p;2p;3p;4p;7p;6p;8g0000j13Tg000Uj10Tg001:j18Tg003ij25Tg00Hcj26Tg00T6j2^Tg004gj27Tg001Xj2JTg00TXR0j3VTg0025j2=Tg002Rj22Tg002oj2@Tg003Lj2PTg004Ej2OTg005Cj2CTg005]j2<Tg006Ej3;Tg00U<j1\Tg00UZj2[Tg006ij1MTg007Hj2LTg00V;j3ZTg0081j3YTg008Zj2XTg009Fj1WTg009fj3UTg00:Fj1TTg00:fj2KTg00;Dj1STg00;bj4HTg00<@j1RTg00<^j1QTg00>mj2GTg00=Ij2BTg00=lj1FTg00>Jj3ITg00@3j4ETg00?Pj3jTg00JFj7iTg00ABj1hTg00Adj2gTg00BFj2dTg00B`j2cTg00CLj3NTg00Cfj3`Tg00DEj4aTg00GXj1bTg00@^j6_Tg00I>j7eTg00Ibj7fTg00Jjj8]Tg00KlR1f0R2'5p=1g00KNR3f1R4;N2p=41712p=9P4g00LJR5g00LiR6P6g00MIR7P2E_p=>P4P5P6P6P7P2g00MiFep=:f2R8P5P6P6P7P4P2Ffp=?P3P4g00RoP2CEp=Df3R9P5P6P6P7P8P4P2G]p=A%12g00O0R:#3R;#3#3#3#3#0#3#3#0#0#8R<,52'61^4<154<R=17<41J4<3V1J8<g00OUR>P0159<17<9P>P3P4%0:R0#8R?%00#0R@#3RA#8RB'=RCf5RD%30RE#3#0RF#8RG,=?RH'2RI'@RJ%0E#0#8RE,=?RK,2D%0@#8R@,=?RL'2RM%0;R;#3#0#0#8RN/PD/2L%0;#8R;,=?RO'2RP'@RQn0100000020000/4CP4f4RR/5<1OCI17CI14JC'615IC14JI'6'Cf6RJ/2H,@CP31<?BRI%9?RS%1B%9C[[RT%1?RUg00P5RVA;?B4UW0RB%1C\V^0URW1<?G%1G%9H[\SA;?G4VVX0U%1H\V^0Up-0RGg00PQRX%\:,[3g00Q=RY#M#M,L35Z31L3Y5Y3g00Q\'X%WXRY3U%TXRXP31K38P4%S3RZCH%R3R[%Q3R\P\P5P6P6P71>\RR5P31G3:g00NI1B3?R:%FA5I3RACE,:\R]5?\1G30R0%FF9I3:5j3/DA,:\1>\D5?\Fi%h6R6P\1B31/D0,:\1>\J5?\P6P]CACA1g\7R7P2P8g00SVR],d>1c28=N>]dA`314CaR1b7b=b>X33X?3X1GX2GW8142C,68124H/5C/69'C%18/6D148C[[^33^?3^1G^2G^8GP2f<R]/5<12]HRH,4D17CHP]PDPJf;RDO7b6b9b:b;b<b@b5W4P2O117<R1OMP17MP14QM'615PM14QP'6'C12JK/2L1PNJ/2L/2O'@P31<?;%1;%9O[\SA;?;4VVX0U%1O\V^0UPIPTPBPW1<?E%1E%9K[\SA;?E4VVX0U%1K\V^0U1<?@%1@%9L[\SA;?@4VVX0U%1L\V^0UPYPXP31K34P4PZCHP[P\P31B3<R[g00RHP0CE,:\P6P\1>\91D0[,:\5?\P6P5CACAP7P1b7b=b>X33X1GX2G17<2168=PR[[^33^1G^2GP2f9/4Cf@RG#1PGPDf?O5b6b9b:b;b<bBbCbDbEb@b5W4P2O1n200210000000021100011000bGbF%b4/4CeWAXH3o"). Qed.
Lemma alloc_margin_mid : forall n, 0 <= n -> alloc_margin n <= 52 * n + 2^17.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSure ()) [] "p'0h02Hah14__p1h24__x1h34__x2h41Hh52H0h67__arithh74__ffh84__p2h96__sat1h:6__sat2h;6__sat3h<6__sat4h=8__varmaph>5__with?2z0h@2HnhA6__sat5hB6__sat6hC6__sat7hD6__sat8hE1bi001bhF2b0hG1np;1p;2p;3p;4p;6p;7p;8g0000j13Tg000Uj10Tg001:j15Tg00T6j2mTg003ij22Tg004gj27Tg001Xj2STg00TXR0j3^Tg0025j2>Tg002Rj24Tg002oj2CTg003Lj2;Tg004Ej2UTg00Hcj26Tg005Cj2ETg005]j2?Tg006Ej3ATg006ij1KTg007Hj2DTg0081j3JTg008Zj2RTg00FIj2HTg009Fj1]Tg009fj3QTg00:Fj1\Tg00:fj2[Tg00;Dj1ZTg00;bj4YTg00<@j1XTg00<^j1WTg00>mj2OTg00=Ij2ITg00=lj1BTg00>Jj3@Tg00ABj1lTg00G5j3kTg00Adj2jTg00BFj2hTg00B`j2gTg00CLj3TTg00Cfj3fTg00DEj4eTg00@3j4LTg00GXj1bTg00@^j6cTg00I>j7dTg00Ibj7aTg00?Pj3`Tg00JFj7iTg00Jjj8_Tg00KlR1f0R2'2p=1f2R3f1R4'4/42p=9g00KNR5?T42p=81712p==P4g00LJR6g00LiR7P7g00MIR8P2Ecp=PP5P4g00NIP2CLp=GP4P6P7P7P8P2g00MiFdp=:P3P6P7P7P8P4P2Fap=FA`542p=<P5P4g00RoP2CLp=NP3P6P7P7P8P4P2Fip=Vf3R9P6P7P7P8P3P4P2G_p=M%12g00O0R6#3R:#3#3#3#3#0#3#3#0#0#5R;,m4124;17;41S4;3^1S3;g00OUR<P0129;17;9P<P5P4%06R0#5R=%00#0R>#3R?#5R@'>RAf5RB%30RC#3#0RD#5RE,>=RF'4RG'CRH%0C#0RC#5RI,>=RJ%0>R>#5RK,>=RL59BRM%0:R:#3#0#0#5RN/;BRO%0:R:#5RP,>=RQ79LRR'CRSn010000002000014OA'2P4f4RO/2;1UAG17AG18HA'612GA18HG'6'Ef6RH/4F,CAP51?=@RG%==RT%1@%=A[[RU%1=RVg00P5RWAA=@4UW0R@%1A\W^0VRX1?=E%1E%=F[\TAA=E4VWX0V%1F\W^0Vp-0REg00PQRYg00Q=RZ#KR[#KR\,D5R]1D5ZRZ5J5AJ5Z]g00Q\R]'R'H%]YR^3Q%\YR_P51[53P4%Z5CYR`%X5Ra%W5Rb1PbORc1O56R61I5=Rd%B?5@5R?'G,:b5Fb1O50R0%BD9@5d'</N?,:b1PbB5Fb5Vb%l7R7Pb1I51/N0,:bP71I5N=k50RD/<?,N6,:bR?CMCM1jb8R8P2P3g00SVRe,h<1g23=T<edAf514CeR1b7b=b>X25X35X1EW8182A,63144F/2A/69'E%131;N9/4A,23[[^25^35^1E^8EP2f<R9/4FRF,8B17AFP9PBPHf;O6b6b9b:b;b<b?b5W4P2O117;O1UMR17MR18SM'612RM18SR'6'EA9HJL1;NH?9LQ'CP51?=P%1P%=Q[\TAA=P4VWX0V%1Q\W^0VPGPUP@PX1?=I%1I%=J[\TAA=I4VWX0V%1J\W^0V1?=K%1K%=L[\TAA=K4VWX0V%1L\W^0V1D5[=J5ZRZ%K\,D51RZ]'H'H=QY^P_P`PaPbP5%BC9@5d,<0%B>9@5dR>'<R0g00RH1<D>%B:9@5d'<RdCL,:b1G60,:b5Fb1G6d,:b9Fbc5VbP7P?CMP8P1b7b=b>X25X35X1EA94JLR11;N4R8?9LQR?'71821'6182?,63'E1;N3/4A,24[^25^35^1EP2f@RE,;N?9LQA9EJL'2PEf9f:O4b6b9b:b;b<bAbBbCbDb?b5W4P2O1n200210000000021100011000bFbE%b4148A'2eW@XG5o"). Qed.
Lemma alloc_margin_big : forall n, 0 <= n -> alloc_margin n <= n + 2^20 + 2^16.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSure ()) [] "p'0h02Hah14__p1h24__x1h34__x2h41Hh52H0h67__arithh74__ffh84__p2h96__sat1h:6__sat2h;6__sat3h<6__sat4h=6__sat5h>6__sat6h?8__varmaph@5__withA2z0hB2HnhC6__sat7hD6__sat8hE1bi001bhF2b0hG1np;1p;2p;3p;4p;6p;7p;8g0000j11Tg000Uj10Tg001:j15Tg00T6j2nTg003ij23Tg004gj27Tg001Xj2QTg00TXR0j3]Tg0025j2<Tg002Rj2:Tg002oj2DTg003Lj2GTg004Ej2TTg00Hcj26Tg005Cj2FTg005]j2>Tg006Ej3ATg006ij1JTg007Hj2ETg0081j3ITg008Zj2PTg009Fj1\Tg009fj3OTg00:Fj1[Tg00:fj2ZTg00;Dj1YTg00;bj4XTg00<@j1WTg00<^j1VTg00>mj2MTg00=Ij2KTg00=lj1=Tg00>Jj3@Tg00?Pj3?Tg00ABj1mTg00Adj2lTg00BFj2kTg00B`j2jTg00CLj3STg00Cfj3hTg00DEj4gTg00E7j2fTg00E`j3eTg00FIj2bTg00G5j3aTg00GXj1cTg00@^j6dTg00@3j4RTg00I>j7`Tg00Ibj7_Tg00JFj7^Tg00Jjj8iTg00KlR1f0R2'3p=2f2R3f1R4':/:2p=4g00KNR5?S42p=81712p=;P4g00LJR6g00LiR7P7g00MIR8P2Edp=NP5P4g00NIP2CRp=HP4P6P7P7P8P2g00MiF`p=9P3P6P7P7P8P4P2F_p=BP5P4g00RoP2CRp=CP3P6P7P7P8P4P2F^p=Uf3R9P6P7P7P8P3P4P2Gip=L%22g00O0R6#1R:#1#1#1#1#0#1#1#0#0#5R;,n4134;17;41Q4;3]1Q3;g00OUR<P0139;17;9P<P5P4%06R0#5R=%00#0R>#1R?#5R@'<RAf5RB%10RC#1#0RD#5RE,<=RF':RG'DRH%0C#0RC#5RI,<=RJ%0>R>#5RK,<=RL54BRM%0:R:#1#0#0#5RN/GB%0:R:#5RO,<=RP74LRQ'DRRn0100000020000/3MP4f4RS/3;1TAG17AG18HA'613GA18HG'6'Ff6RH/:F,DAP51>=IRG%;=RT%2I%;J[[RU%2=RVg00P5RWAA=I4UW0RI%2J\W^0VRX1>=@%2@%;A[\TAA=@4VWX0V%2A\W^0V1>=KR@%2K%;L[\TRYAA=K4VWX0VRK%2L\W^0VRZ1>=E%2E%;F[\TAA=E4VWX0V%2F\W^0Vp-0REg00PQR[g00Q=R\#JR]#JR^,E51E5]1E5\R\5I5R]5I5g00Q\R_'P%\[R`3O%[[RaP51Z53P4%Y5CXRb%W5Rc%V5Rd1NdSRe1M56R61K5=Rf%=?5@5R?'H,9d5Bd1M50R0%=D9@5f5?5/C?,9d1NdB5Bd5Ud%m7R7Pd1K51/C0,9dP7%=C9@5f9?50%=>9@5fR>5?5RC,C6,9dRBCLCL1ld8R8P2P3g00SVR?,k<1j23=S<?dAh514CgR1b7b?b@X25X35X1EW8182A,631:4F/3A/69'F%23A49JL,33[[^25^35^1E^8EP2f9R9f@R?/:FRF'817AFP?P9f:f?O6b6b9b:b;b<b=b>bCbDbAb5W4P2O117;S1TMQ17MQ18RM'613QM18RQ'6'FA4HJL1GNH?4LP'DP51>=O%2O%;P[\TAA=O4VWX0V%2P\W^0VPGPUPIPXP@PYPKPZ%1:#1#5,f5=e5\%J^,E55I5/P_,b]=O[`PaPbPcPd1H6C,9d9Bde1K5N=a50=?5>%=:9@5f5?5Rf/CC,9d1H6f,9d5Bd5UdP7PBCLP8P1b7b?b@X25X35X1EA44JLR1,82,631GN4?4LPR8/311828'6'FA43JL,34[^25^35^1EP2f>RE?4JL1GNE?4LP'7PEf7f8O4b6b9b:b;b<b=b>bAb5W4P2O1n200210000000021100011000bFbE%c4/31eWBXG5o"). Qed.

(* [comment removed for export] *)
Definition ROOM_BCAP : Z := 2^33.
Definition ROOM_KMAX : Z := 420000.
Definition ROOM_NMAX : Z := 2^28.

(* [comment removed for export] *)
#[export] Existing Instance aic_base.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithLayout.
Context {AL : AllocLayout} {CL : CallocLayout}.

Class AllocSure := {
  asr_calloc :: AllocCalloc;

  (* [comment removed for export] *)
  aroom : AS -> VmMaps -> Z -> Z -> Prop;
  aroom_mono : forall A h k b k' b',
      aroom A h k b -> 0 <= k' <= k -> 0 <= b' <= b -> aroom A h k' b';
  aroom_nonneg : forall A h k b, aroom A h k b -> 0 <= k /\ 0 <= b;
  (* [comment removed for export] *)
  aroom_init : forall h0 k b,
      init_ledger h0 -> ROOM_BCAP <= Z.max ROOM_BCAP (vm_limit h0) ->
      0 <= k <= ROOM_KMAX -> 0 <= b <= ROOM_BCAP ->
      aroom A0 h0 k b;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ai_malloc_l : forall (fx : FPState) A m md regs (n : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2^61 ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q))
            \/ (bv_unsigned res <> 0 /\ live A res = None /\ live A' res = Some n /\
                (forall q, q <> res -> live A' q = live A q) /\
                (forall i, 0 <= i < round16 n -> owned A (at_ res i) \/ m (at_ res i) = None)) ) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, live A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          (* [comment removed for export] *)
          (forall k b, aroom A (m_vmmaps md) k b -> 1 <= k -> alloc_margin n <= b ->
                       aroom A' vm' (k - 1) (b - alloc_margin n)) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_malloc_pc m al_rom) md) S;

  ai_free_l : forall (fx : FPState) A m md regs (p ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = p -> (p = Z_to_bv 64 0 \/ exists n, live A p = Some n) ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs',
          ainv A' m' vm' ->
          (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          live A' p = None -> (forall q, q <> p -> live A' q = live A q) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, live A' q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          vm_live_bytes vm' <= vm_live_bytes (m_vmmaps md) ->
          (* [comment removed for export] *)
          (forall k b, aroom A (m_vmmaps md) k b -> aroom A' vm' k b) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_free_pc m al_rom) md) S;

  ai_calloc_l : forall (fx : FPState) A m md regs (cnt sz : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
      0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= cnt * sz < 2^61 ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - CALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q))
            \/ (bv_unsigned res <> 0 /\ live A res = None /\ live A' res = Some (cnt * sz) /\
                (forall q, q <> res -> live A' q = live A q) /\
                (forall i, 0 <= i < round16 (cnt * sz) -> owned A (at_ res i) \/ m (at_ res i) = None) /\
                (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0))) ) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - CALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, live A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          (* [comment removed for export] *)
          (forall k b, aroom A (m_vmmaps md) k b -> 1 <= k -> alloc_margin (cnt * sz) <= b ->
                       aroom A' vm' (k - 1) (b - alloc_margin (cnt * sz))) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_calloc_pc m al_rom) md) S;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ai_malloc_sure : forall (fx : FPState) A m md regs (n k b : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2^61 ->
      (* [comment removed for export] *)
      aroom A (m_vmmaps md) k b -> 1 <= k -> alloc_margin n <= b -> n <= ROOM_NMAX ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          bv_unsigned res <> 0 -> live A res = None -> live A' res = Some n ->
          (forall q, q <> res -> live A' q = live A q) ->
          (forall i, 0 <= i < round16 n -> owned A (at_ res i) \/ m (at_ res i) = None) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k' i, live A q = Some k' -> 0 <= i < k' -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          aroom A' vm' (k - 1) (b - alloc_margin n) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_malloc_pc m al_rom) md) S;

  ai_calloc_sure : forall (fx : FPState) A m md regs (cnt sz k b : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
      0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= cnt * sz < 2^61 ->
      (* [comment removed for export] *)
      aroom A (m_vmmaps md) k b -> 1 <= k -> alloc_margin (cnt * sz) <= b -> cnt * sz <= ROOM_NMAX ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - CALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          bv_unsigned res <> 0 -> live A res = None -> live A' res = Some (cnt * sz) ->
          (forall q, q <> res -> live A' q = live A q) ->
          (forall i, 0 <= i < round16 (cnt * sz) -> owned A (at_ res i) \/ m (at_ res i) = None) ->
          (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0)) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - CALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k' i, live A q = Some k' -> 0 <= i < k' -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          aroom A' vm' (k - 1) (b - alloc_margin (cnt * sz)) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_calloc_pc m al_rom) md) S
}.

End WithLayout.
