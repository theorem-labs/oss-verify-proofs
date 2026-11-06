(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run StackLayout.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import LiaTuning InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RunConst () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02c59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib3Lib8RunConst7ATOP_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib8RunConst7ATOP_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib4Init5Logic3and00i59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib3Lib8RunConst8ATOP_MINC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib8RunConst8ATOP_MAXC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib3Lib7InitMem:entry_atopC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib7InitMem<entry_secretC1?~~~~~~~~~~~~~~~".
Open Scope Z_scope.

Class runConstT : Type := RunConst {
  ATOP : Z;
  SECRET : Z;
  CAN : word;
  ATOP_lo : 0x7fff7f800000 <= ATOP;
  ATOP_hi : ATOP <= 0x7FFFFF800000;
  ATOP_al16 : ATOP mod 16 = 0;
  SECRET_rng : 0 <= SECRET < 2^64
}.

(* [comment removed for export] *)
Definition ATOP_MIN : Z := 0x7fff7f800000.
Definition ATOP_MAX : Z := 0x7FFFFF800000.

Lemma ATOP_range {rc : runConstT} : ATOP_MIN <= ATOP <= ATOP_MAX.
Proof.
ltac2:(KReplay.run1 (kr_t_RunConst ()) [] "h02rcp;1p;2p;4g0000j10Tg000Uj16Tg0013j1;Tg001ij23Tg002Ej11Tg002jj18Tg003cj19Tg004\j4:Tg0057j2<Tf0R0#1#1p==%10#1#1#1p=2%00#0p=5%00#0#0#0p=7%00#0#0#0#0#0#0#0p=4g005RR1g006O#=#2#2#2R2#0#2#2#0#5#7#4#4#6%;0R3'3%12#2#2#0#5#7#4#4#6,33%80%90C:g0074/33g007n,33'<eX01P0O1W0o"). Qed.

(* [comment removed for export] *)
Lemma entry_atop_lo : forall en, valid_sp (en_sp en) -> 0x7fff7f800000 <= entry_atop en.
Proof.
ltac2:(KReplay.run1 (kr_t_RunConst ()) [] "h02H0h14__x1h21Hh31Lh41Mh57__arithh64__ffh78__varmaph85__with92enp;1p;2p;4p;3p;8p;7g008hj12Tg009Zj1VTg0000j10Tg00:Oj1UTg00:mj23Tg001ij21Tg000Uj15Tg00;Wj2:Tg0057R0j2ATg00<7j1<Tg00=2j1TTg00=Rj1STg00>2j2QTg00>Pj1NTg00>nj1MTg002Ej14Tg00?Yj28Tg00@<j2JTg00@_j4@Tg00AJj1ITg00Alj3?Tg00BOj3HTg00C2j8KTg00CVj2LTg00D8j2GTg00DRj2FTg00E>j3BTg00EXj3OTg00F7j4PTg00Fij2CTg00GFj2DTg00Gcj7RTf0R1#0#0p=9g00HGR2g00HeR37B1p=;%41#4p=E%41#4#4#4p=6%01#0#0#0p==%01#0#0#0#0#0#0#0p=7f1R4g00ICR5g00IbR6P6g00JBR7P1g00JbFRp=>g00KB%21#VP0g00L:R8g006OR9#0#9R:#0R;#9R<#UR=%24'3R>'1g00M5R?,1>%5;R;,:>#;'A%E9#6#6#6R>#0#6#6#0#9#=#7#7#5R@f2RA#<'1P1f3#2,3=,18f4#2,3=R8/1?1:8;#;'AP0f5#2,3=R0/1?1:0;#;f6R0#<,1@P1f7#2,3=/1?f8#2,3=/:;#;g00N0R;#T%S;1Q24%N2%M2R;P5P6P6P7P2%4>#0#9#=#7#7#7#5R>,82g00N\R51J29R9C@,>;%I6P2182@P5%5:R:,82%=<#5R<,82R55?2=?259H29C@,>;GK1L;7P1PAg00OCR;g00OcR7'G1F1A=B;7dAO234CPb6b7b8X1211>11C:</C<,D4,1@[^12P1f:#2,3=P0O2b5f9#<,1@eW4W2P4P1O2n2001000000121000000W0W3P4P1O2n2001000000121000000W0W9o"). Qed.
Lemma entry_atop_hi : forall en, valid_sp (en_sp en) -> entry_atop en <= 0x7FFFFF800000.
Proof.
ltac2:(KReplay.run1 (kr_t_RunConst ()) [] "h02H0h14__x1h21Hh31Lh41Mh57__arithh64__ffh78__varmaph85__with92enp;1p;2p;4p;3p;8p;7g008hj12Tg009Zj1VTg0000j10Tg00:Oj1UTg00:mj24Tg001ij21Tg000Uj16Tg00;Wj29Tg0057R0j2ATg00<7j1<Tg002Ej13Tg00=2j1RTg00=Rj1QTg00>2j2OTg00>Pj1NTg00>nj1MTg00@<j2JTg00?Yj28Tg00@_j4@Tg00AJj1ITg00Alj3?Tg00BOj3HTg00C2j8KTg00CVj2LTg00D8j2GTg00DRj2FTg00E>j3BTg00EXj3ETg00F7j4PTg00Fij2CTg00GFj2DTg00Gcj7STf0R1#0#0p=;g00HGR2g00HeR37B1p=:%31#3p=T%31#3#3#3p=7%01#0#0#0p==%01#0#0#0#0#0#0#0p=5f1R4g00ICR5g00IbR6P6g00JBR7P1g00JbFSp=>g00KB%21#VP0g00L:R8g006OR9#0#;R:#0R;#;R<#UR=%24'4R>'1g00M5R?,1>%6;R;,9>#:'Af2R>#<%39#T#7#7#7#7#7#0#;#=#5#5#6R@'1P1f3#2,4=,18f4#2,4=R8/1?198;#:'AP0f5#2,4=R0/1?190;#:f6#</1@P1f7#2,4=/1?f8#2,4=/9;#:g00N0R;#R%Q;1O24%N2%M2R;P5P6P6P7P21J29R9g00N\R5%=<R<#0#=#5#5#5#5#6R?,82C@,>;%I6P2%6:R:,82%6<R<,82R65?2=?269H29P5182@C@,>;GK1L;7P1P>g00OCR;g00OcR7'G1F1>=B;7dAE234CPb6b7b8X12111?1C:</C<,D4/1@[^12P1f:#2,4=P>O2b5f9#</1@eW4W2P4P1O2n2001000000121000000W0W3P4P1O2n2001000000121000000W0W9o"). Qed.
Lemma entry_atop_al16 : forall en, valid_sp (en_sp en) -> entry_atop en mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RunConst ()) [] "h02H0h12H1h22H6h34__x1h44__x2h54__x3h64__x4h74__x5h81Hh92H2h:2H3h;2H4h<2H5h=2H7h>2H8h?2H9h@1LhA1MhB7__arithhC4__ffhD8__varmaphE5__withF2enhG1qhH2q0hI1rhJ2r0p;1p;2p;3p;4p;6p;7p;8g008hj1TTg009Zj1nTg0000j14Tg00:Oj1\Tg001ij22Tg000Uj1HTg00;Wj21Tg0057R0j26Tg00<7j1FTg00Fij2:Tg00GFj27Tg00PCj2UTg00Pdj1lTg00Q=j2;Tg00QZj2CTg00R7j2QTg00R^j25Tg00S:j2STg00Saj2PTg00TGj2OTg00Tmj2_Tg00D8j2NTg00UNj1^Tg00Ulj2]Tg00VMj1>Tg00Vlj2=Tg00WUj3GTg00X>j2[Tg00Xjj2MTg00=2j1ZTg00YVj3YTg00=Rj1XTg00Z6j1WTg00>2j2ETg00ZTj4LTg00>Pj1VTg00>nj1mTg00?Yj2DTg00[2j6kTg00AJj1jTg002Ej1KTg00@<j2ATg00Alj3BTg00[Vj3RTg00@_j4JTg00\9j7gTg00BOj3fTg00CVj2eTg00DRj2cTg00E>j3ITg00EXj3dTg00F7j4bTg00:mj2aTg00\]j3hTg00Gcj7`Tg00C2j8iTf1R1f0R2#T'ap=0g00HGR3g00HeR47I2p=3AI312p=<Ah312p=8P3P1g00]FP2CJp=@P1g00ICR5g00IbR6P6g00JBR7P2g00JbF`p=9f3R8P5P6P6P7f2R9P1P2Gip=?g00KB%T2#nP0g00L:R:g006OR;#4R<#4#4R=#4R>#4#4R?#\R@/01RA'2g00M5RB,2A%H>R>,1A#3'6%F9/1>#3P210@8,2:f4R:,0@RA/2B11A>#3'6P0f5R0,0@RA/2B11A>#3f6RA#F/1>#3P2f7,0@/2Bf8RB,0@/1>#3f9RC,0@%H=R=%4?#4#4#4#HR?':/:?RD'7/U>%3>RE#lRFf:RG,0@/7DRH1;H>,:>11H>'C'<[1QH>154>RHf;RI,0@/7DRJ/1>RK,2415K>'6[1SJ>15>4RJf<,0@/7DRK/1>RL,5>12L4'6[1PK>f=RK,0@/7DRL/;>#3\E1OL>f>,0@/7DRL/1>/<L\E1;L>P3f?,0@/7D/1>P3f@RL,0@/U>fARM,0@RN1;N>,:>11N>'C'<\F1QN>fB,0@RN/1>RF,2415F>'6\H1SN>fC,0@RN/1>RF,5>12F4'6\J1PN>fD,0@RN/;>#3\E1ON>fE,0@RN/1>/<N\E1;N>P3fF,0@/1>P3P0g00]m1_4>'NPHeRHO11242152>'6PKPHO1124B15B>'6g00N0RB%^;,]3RHg00^SRK#>RN#>RJ#>RF#>#>RO,=35G31=3FRF1=3JRJ1=3NRN9G3H'8'8'8%>O,=3AG3HF18JN'8'81=3K,8Ng00_2'['M'M%ZB3Y%XBP3P3%W3P01E3:CLP1P31E38P91E30CLCL%V3%m3RBPBPBP5P6P6P71D3>RN1D34RK'@,9BEkRJ%j6RF%K;RH,A3RO%KH,A39B3N%K<,A3R<5R3'@,9BC?PFPBPBP5P6P6P7P3PKg00N\1A3;R;CJ,9BP3P;g00_^PNCJ,9BFgPFPBPBPJPF1D3=1D3?R?5B3=B3?9f3O%4H,A39B3N=R3;'@,9BC?PFPB1@<K,9BPF1@;K,9BC?C?C?C?1eB7P2P9g00OCRBg00OcR7'N1c29=IB7dAd341CbbCbDbEX33X43X53X63X73g00`E\ERE1:>0/C8,<9[1241151>'617:D1:>A/C8'<\E%30%3:[[[[^33^43^53^63^73P2P:PIP8fJ,0@PGPCP1PLPMO9bBb1b2bJbHb?b>b=b2b<bIbGb;b:b9b1b0%FC/1>#3eWAW8P1P2O2n2001000000121000000W0W@P1P2O2n2001000000121000000W0WFo"). Qed.

Definition run_consts_of (en : ExecEntry) (c : word) (V : valid_sp (en_sp en)) : runConstT :=
  {| ATOP := entry_atop en; SECRET := entry_secret en; CAN := c;
     ATOP_lo := entry_atop_lo en V; ATOP_hi := entry_atop_hi en V; ATOP_al16 := entry_atop_al16 en V;
     SECRET_rng := draw_secret_range (en_draw en) |}.

Lemma run_consts_of_ATOP : forall en c V, @ATOP (run_consts_of en c V) = entry_atop en.
Proof.
ltac2:(KReplay.run1 (kr_t_RunConst ()) [] "h01Vh11ch22enp;1p;2g0000j10Tg00:Oj16Tg00`bj12Tg008hj11Tg009Zj15Tg00<7j14Tg00D8j23Tg00KBg006O#0#0#0#0#0#0#6#2f1#1#5g00HGf2#4'3W0W1W2o"). Qed.
Lemma run_consts_of_SECRET : forall en c V, @SECRET (run_consts_of en c V) = entry_secret en.
Proof.
ltac2:(KReplay.run1 (kr_t_RunConst ()) [] "h01Vh11ch22enp;1p;2g0000j10Tg00:Oj16Tg00`bj12Tg008hj11Tg009Zj15Tg00aEj14Tg00D8j23Tg00KBg006O#0#0#0#0#0#0#6#2f1#1#5g00HGf2#4'3W0W1W2o"). Qed.
Lemma run_consts_of_CAN : forall en c V, @CAN (run_consts_of en c V) = c.
Proof.
ltac2:(KReplay.run1 (kr_t_RunConst ()) [] "h01Vh11ch22enp;1p;2g0000j10Tg00:Oj15Tg00`bj12Tg008hj11Tg009Zj14Tg00D8j23Tg00KBg006O#0#0#0#0#0#0#5#2R0f1R1#1#41301W0W1W2o"). Qed.
