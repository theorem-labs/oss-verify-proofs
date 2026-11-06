(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg Hoare HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_HeIface () := "C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rC56Stdlib6ZArith6BinInt1Z5max_lc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeIface4cszRC13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z8le_max_lC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~C35stdpp7tactics<f_equal_helpK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega6VarMap1t03c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeIface6debitRC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeIface7refundRC13~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib4Init9Datatypes4prod00K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init5Logic2or01c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeIface4fitsC13~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z7max_lubC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic4True00".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

Definition NREQ : Z := 2 ^ 35 + 2 ^ 32 - 2 ^ 16.   (* [comment removed for export] *)
Definition NREQA : Z := 2 ^ 30 - 2 ^ 16.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cszR (n : Z) : Z := Z.max (2 ^ 20) ((n + 20 + 4095) / 4096 * 4096).

Definition credit_okR (cr : credit) (n : Z) : Prop := 1 <= fst cr /\ cszR n <= snd cr.
Definition debitR (cr : credit) (n : Z) : credit := (fst cr - 1, snd cr - cszR n).
Definition refundR (cr : credit) (n : Z) : credit := (fst cr + 1, snd cr + cszR n).

Lemma cszR_small n : 0 <= n <= 2 ^ 20 - 20 -> cszR n = 2 ^ 20.
Proof.
ltac2:(KReplay.run1 (kr_t_HeIface ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h52H0h62H1h72H2h82H3h92H4h:4__p1h;6__sat0h<1nh=1qh>1rh?1Hh@2Hnp;1p;2p;3p;4p;6p;7p;5p;8g0000R0p4p711g000OR1p4p73101p8g0013j1>Tg001Xj13Tg0026j18Tg002[j2WTg0038j2DTg003Uj2:Tg0041j2=Tg004Lj2;Tg004ij2ATg005Fj1fTg005fj1`Tg006Fj1XTg006dj1VTg007Bj1UTg007mj2FTg008Pj2STg0092j2RTg009Lj2QTg00:8j36Tg00:Rj3OTg00;1j4NTg00;cj22Tg00<?j2MTg00<]j6LTg00=Aj2KTg00=dj3JTg00>Gj7ITg00>kj1PTg00?Mj3CTg00@0j3HTg00@Sj5TTg00A?j2eTg00B0j2dTg00BQj1cTg00Bjj2<Tg00CJj2BTg00Cgj2_Tg00DNj2YTg00E5j2ZTg00E[j2[Tg00FAj5\Tg00Foj3]Tg00GNj1^Tg00HZj4GTP1j7aTg00IEj8bTg00IiR1f0R2':p=5%>2#>p=0%82#8p=9f2R3f1R4'B/B2p=1g00JGR5/F2p=7P5P4g00JeP2CGp=@P4P0g00KLR6P6g00KlR7P2g00LLFap=4P5P4g00LlP2CGp=?f3R8P0P6P6P7P3P4P2Gbp=E%52g00MSR9#>R:#3%8:#0#3R;'WR</D;,:2'=%0:#0#0R:#>R=#0#0R>#0#0#0#0#3R?%89#9#9#9#9#9#3R@914;RA%3>R>';RB/A>PAP>%8:#3R:g00N8RC#fRD%`CRC%X5RE%V5RF%U5RG1F51RH%7>RI'@'41SG7RJP2P3g00NdRKg00ODRL'R1Q23=6KLdAO514CNRLb1b2b3121>RKP2b0p-0RMPDPC1M54RNPFPGPGP0P6P6P7PGP0P6P6P7P8EL1K59R9%7?%7;R75J5'?,4GFI%P6R6AC597%7@5C5%7:R79H5I'@,4GCEPJPLb1b2b3X45W:1D?;,:2,=41A>:,2A[^45^:MP2%53P3P4O3b0DT12B:A13;@RB/;>%3=R=P>1eB>RM%5B%5>RBf4?1;@RA/;>R?#5[[R0A18;@/d>R8A65>1RO#c1A>?1<A>'B965A[R?1_A>RAf5?1;@RP/<>RQ#512Q>'=\KRK1YP>RP12>1f6?1;@RQ/<>RR,2>1:R1'=[RR1ZQ>RQf7?1;@RS/;>=651\OR11[S>RSf8?1;@RT/<>=65T\ORO1;T>RTP5f9RU?1;@/<>R>P5PDPCPEPF1?HI,4GPJPLb1b2b3PBP2b0b>b=b9b8b7b6b5b;PMP0P8P?PAPKPPPRPQP1PSPOPTP5P>P5PDPCPNPFPG1@97,4GP6%7=,?9,4GCEPJPLb1b2b3X45122:1:4=[^45P2P3PUO2b0b>b=b9b8b7b6b5b;D\b?3]%^4=65<eW@X<5P2O1X<5o"). Qed.

Lemma cszR_ge n : 2 ^ 20 <= cszR n.
Proof.
ltac2:(KReplay.run1 (kr_t_HeIface ()) [] "h01np;1p;2g0013j13Tg001Xj14Tg0026j12Tg002[j2;Tg00CJj25Tg004Lj2:Tg004ij29Tg00Odj27Tg00GNj16Tg003Uj28Tf0R0#3#3p=0%20#2p=1g00JGR1g00MSR2#3R3#4%23#0#4R4';R51504%22#1#1#1#1#1#4'5%33#0#0#0#0#0#4R3':/93'7%60,85eX01P0O1W0o"). Qed.

Lemma refund_debit cr n : refundR (debitR cr n) n = cr.
Proof.
ltac2:(KReplay.run1_chk (kr_t_HeIface ()) [] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h62crh71nh81bh91ki001pi011zp;1p;3p;2p;4p;8p;7g00PFR0p4p70g00QQR1p4p7210p8g001Xj1TTg00GNj15Tg00:8j31Tg00Qnj3<j2Ej4PTg0092j2?Tg005Fj1CTg005fj1ATg00<?j2:Tg006dj1STg007Bj1RTg00=Aj2@Tg007mj2LTg00=dj3>Tg00?Mj38Tg00HZj4=Tg008Pj2KTg009Lj2JTg00:Rj3ITg00;1j4HTP1j8;Tg006Fj1FTg00RNj4GTg0013j1DTg0038j26Tg00CJj27Tg00Rlj2BTg00T:j2MTg00UIj3NTg00Ufj3OTg000Oj7QTg00JGR1f0R27N1p=3f2R3f1R4'6/72p=0AO112p=4P1P1P4P2CPp=2P4g0000g00KLR5P5g00KlR5P2g00LLFQp=9g00VCP1P1%32g00MSR6#TR7;07%42%54R8;08'2=102P4P1P0A0477R89<11A<114f4#5R9=029P2P1P0\1R:1E11R;P;P8P4P:\1/?;g00N8R;#CR:%A;R;1:14%S1R8%R1R<P11@16R=1L17R>5>1=81>g00VcR>P=C='91K<5R5P2P3g00NdR?g00ODR@'?1J23=1?@dg00Ii=I14CHR@b2b3b4X01A0277=112^01P2P3O1b1G;P:P;P11:13P4%F1CGP8P1%D6,@1R69>1==816P>P=C=,9<P5P@b2b3b4X01X51A0244=112^01^51P2f5#5P4O2b1G;1242R@#3?077%4@?099'2=10@eX81X91P4P2O2n2001100000121101101%34/67%44%52R@'6'2R9#3/77%49/7@'2=104e1B42/M2=104eX71X60P4P2O2X71X60o"). Qed.

(* [comment removed for export] *)
Definition fits (lim n : Z) : Prop := n < 131052 \/ (n + 20 + 4095) / 4096 * 4096 <= lim.

Lemma fits_small lim n : n < 131052 -> fits lim n.
Proof.
ltac2:(KReplay.run1 (kr_t_HeIface ()) [] "h03limh11nh21Hp;1p;2p;3g0026j13Tg0013j12Tg001Xj14Tg00;cj26Tg00CJj25Tg004Lj2:Tg004ij29Tg003Uj28Tg00WJj37Tf0R0#3#3p=1%20#2p=0g00JGR1g00MSR2#3#1#1#1#1#1R3#2#1#0#4R4,60f1R5/64%22R2#3#0#4,55%43'5%22#0#0#0#0#0#4R2':/92f2'8;70W2X11X01P5P0O2X11W0o"). Qed.
Lemma fits_le lim n : fits lim n -> 131072 <= lim -> n + 20 <= lim.
Proof.
ltac2:(KReplay.run1 (kr_t_HeIface ()) [] "h04__x1h14__x2h21Hh32H0h42Hlh57__arithh64__ffh74__p1h88__varmaph95__with:4__x3h;4__x4h<3limh=1nh>2H1h?2H2h@2H3hA2H4hB1qhC1rp;2p;1p;3p;4p;6p;7p;8g00Wdj2dTg0026j1@Tg0013j17Tg001Xj1<Tg00;cj25Tg004Lj2=Tg004ij2>Tg003Uj20Tg00CJj26Tg00Y0j1ITg00YOj2BTg00Z8j3GTg00Zaj2KTg005Fj1\Tg00[Mj3MTg005fj1YTg00<?j2FTg006Fj1XTg00RNj4ETg006dj1WTg007Bj1VTg007mj2:Tg00=Aj2?Tg00>kj1UTg00?Mj3HTg008Pj2QTg0092j2PTg009Lj2OTg00:8j39Tg00:Rj3RTg00;1j4NTg00B0j2STg00BQj1TTg00Bjj2;Tg00Cgj2cTg0041j2JTg00DNj2bTg00E5j2aTg00E[j2`Tg00<]j6^Tg00>Gj7]Tg00HZj4ATg00[mj6[Tg00@0j3LTg000Oj7_Tg00IEj8ZTf0R0#@#@p=8%70#7p=1f2R1f1R2'6/60p=3g00JGR3P2g00LlP0CAp=DP2g0000R4g00KLR5P5g00KlR6P0g00LLF_p=2P3P2g00JeP0CAp=Cf3R7P4P5P5P6P1P2P0GZp=41d20g00\Qg00MSR8#@R9#8#8#8#8#8R:#7#8#1#<R;,52R<%78R=#@#1#<R>%<:R:532%7=R?#1#1#1#1#1R@#<RA'=/>A/01%7@#1#1#<R@/07167>f4RB'0RC[P0151;10@BRDg00N8REg00\kRF#IRG#IRH,B31B3G1B3F5G35G3RFg00]JRG'K%\ERI3M%YERJP31F31P2%X3RKCE%W3RL%V3RM1:3@1?3=R='D,2M%U5RNPM1?38R81:3;'C,2MPN1:3>9H38R8/D=,2MR;C4C41QM6ROP0P1g00NdRPg00ODRQ'P1O01=9PQdg00IiRQ=R32CNRPb6b8b9X03X1310@2161>R@/07\<[^03^13P0f6R<f5RRP2P1O4b5W4W2P0O116@:R@/=A/>A/07A3B>:/SAA93AQRS#TA3R>:RT1=TA,>A1;TA'6593[1cTA15QARTA3<>:RU/;ARV,0Q15VA'J[1bUA15AQf7RU?3>:RV/;ARW,5A10WQ'J[1aVAf8?3>:RV/=A=93Q\S1`VAf9RV?3>:RW/;A=93W\S1=WAP3f:?3>:/;AP3p-0R>%IH,B3=G3F/KG=MEIPJP3P31F3BP1PKCEP21F37CEPLPMPM1:3QRL1:3ARK'C,2MPNPMP4P5P5P6PMP4P5P5P6P<E^1?3?R?/CK,2MF]C4PNPMPMPMP4P5P5P6P3PKg00VcR6PLCA,2ME[PNP31:3:9H38P61?39R99L3K=H3?CA,2MC4PNPMAL39K/D=,2MPNP;C4C4C4POPPb6b8b9X03X13X:3X;3W715BA,JR\Tg00^6\S1>AB/6R993@[1>BA/07PC[[[^03^13^:3^;3^7>P010Q2P2P1f=f<P<PUPVO8b5bCbBbAb@b?b>b3X4DW2P0O1n200100000021100011000W3X=3X<3P2P0O2X=3X<3o"). Qed.
Lemma fits_mono lim lim' n : fits lim n -> lim <= lim' -> fits lim' n.
Proof.
ltac2:(KReplay.run1 (kr_t_HeIface ()) [] "h01Hh12H0h22Hlh34__x1h44__x2h54__x3h63limh74lim'h81nh92H1h:2H2h;2H3h<2H4h=7__arithh>4__ffh?6__sat0h@8__varmaphA5__withB1qhC1rp;2p;1p;3p;4p;7p;8g00Wdj2FTg0026j1;Tg0013j17Tg001Xj1:Tg00;cj22Tg004Lj26Tg004ij25Tg003Uj20Tg00WJj3HTg00A?j2GTg00B0j2aTg00:8j39Tg00BQj1XTg00Bjj28Tg00CJj2>Tg00Cgj2VTg0041j2DTg00DNj2UTg00E5j2TTg00E[j2PTg00Y0j1CTg00YOj2<Tg00Z8j3BTg00Zaj2OTg005Fj1NTg00[Mj3LTg005fj1KTg00<?j2ATg00RNj4JTg006dj1ITg007Bj1MTg00=Aj2@Tg00>kj1QTg007mj2RTg00@0j3STg008Pj2`Tg0092j2_Tg009Lj2^Tg00:Rj3]Tg00;1j4\Tg00^Sj3YTg00HZj4ZTg000Oj7[Tg00IEj8WTf0R0#;#;p=4%70#7p=3f2R1f1R2'>/>0p=1g00JGR3P2g00LlP0CZp==P2g0000R4g00KLR5P5g00KlR6P0g00LLF[p=?f3R7P4P5P5P6P1P2P0GWp=E1F10g00\Qg00MSR4#;R8#4#4#4#4#4R9#7#4#3#:R:,22%74R;#;#3#:R<%:9R9512%7;#3#3#3#3#3#:R='6/5=/07f4R>/071F>7[P0121:f5R?/0>R@12>:R:A1><9RA/6=/5=/0?RB;H2W2W0P0O1A11<9/6=/5=/0>1GA=g00IiR>/0A10>=f6?1<9RA/6=RC,0>[[A1?<9/a=A93=>R?#X15=C18A='>993A[1VA=12>=f7?1<9RA/8=RC,0>12C='D[1UA=12=>f8?1<9RA/8=RC,2=10C>'D[1TA=f9RA?1<9RC/6==93>\?1PC=f:RC?1<9RD/8==93D\?16D=P3f;?1<9/8=P3g00N8R9g00\kR<#CRD#C,<31<3D1<3<5B35B3g00]J'O%N93L%K9P31A31P21A37CJ%I3%M3R91@38R81@3;R;'=,?9%Q5R5P91@341R3=5S3R4/=8,?9P51=4;,?9CECE1`96P0P1g00NdR9g00ODR6'_1^01=996dA]3>2C\b>b@bAX33X43X531012152=/07151=/07[[^33^43^53P0f?f>P1PAPCO5b=bCbBb<b;b:b9b1b?9Y:BX2@W0P0O1n200100000021000011000W1X83X73X63P1P2P0O3X83X73X63o"). Qed.
Lemma fits_cszR lim n : fits lim n -> 2 ^ 20 <= lim -> 0 <= n -> cszR n <= lim.
Proof.
ltac2:(KReplay.run1 (kr_t_HeIface ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51Hh62H0h72Hlh82Hnh94__p1h:4__x2h;4__x3h<4__x4h=3limh>1nh?2H1h@2H2hA2H3hB2H4hC2H5hD6__sat1hE1qhF1rp;2p;1p;3p;4p;5p;6p;7p;8g00Wdj2nTg0026j1?Tg0013j1CTg001Xj16Tg00;cj24Tg004Lj29Tg004ij27Tg003Uj21Tg002[j2RTg00GNj1OTg005Fj1lTg005fj1hTg006Fj1dTg006dj1^Tg007Bj1]Tg007mj2LTg008Pj2ZTg0092j2YTg009Lj2XTg00:8j38Tg00:Rj3WTg00;1j4VTg00<?j2ITg00=Aj2DTg00>kj1STg00?Mj3>Tg00@0j3HTg00^mj5QTg00A?j2PTg00B0j2TTg00BQj1UTg00Bjj2@Tg00CJj2GTg00Cgj2mTg0041j2JTg00DNj2kTg00E5j2jTg00E[j2gTg00Y0j1BTg00YOj2ATg00_Yj1cTg00`7j2bTg00`Xj3_Tg00Z8j3ETg00Zaj2`Tg00[Mj3aTg00RNj4NTg00<]j6eTg00>Gj7fTg00HZj4FTg00[mj6\Tg00aAj5MTg000Oj7[Tg00IEj8iTf0R0#?#?p=:%C0#Cp=2f2R1f1R2'G/G0p=0g00IiR3/10p=<g00JGR4/L0p=;P4P2g00JeP0CFp=KP2g0000R5g00KLR6P6g00KlR7P0g00LLF[p=3P4P2g00LlP0CFp==f3R8P5P6P6P7P1P2P0Gip=51n20g00\Qg00MSR9#?R:#:#:#:#:#:R;#C#:#2#6R<,42%C9R=#?#2#6R>%6;R;502R?%C=R@#2RA#2#2#2#2RB#6RC'9/7C/11%6=/R>RD/18%<8f4RE#Of5RF'1[[P0141<11DERG%<ERHPDA0F>;RI/9CRJ/7CRKf6RLP2PIPC%?A#6RAg00N8RI#lRM%hIRN%d4RO%^4RP%]4RQ1L43RR%;CRS'K'3RT1ZQ7RUP0P1g00NdRVg00ODRW'Y1X01=8VWdAW432CVRWb2b3b4143CRVP0b1PMPN1I42PPPQ1D49RX%;<RY'K,3Q%S6RZ%;>R[9>4X%;;R\5>4%;A9H4S'=,3QC5PUPWb2b3b4X04140<17CA,1?[^04P0PLP8O2b1DQ11JAA0L>;RA/PC%<A%<Cf8?0>;RA/9CRJ#<[[f7R??0>;/TCA84C3R]#U17CJ1@AC'G984A[1mACf9?0>;RA/@CRJ#<14JC'J\V1kAC14C3f:RA?0>;RJ/@CR^,4C11^3'J[1jJCf;RJ?0>;R^/9C=843\]1g^Cf<R^?0>;R3/@C=843\]193CP4f=?0>;/@CP4p-0R3g00\kR_#BR`#BRa#B#BRb#B,A4%c9,b41A4b5_41A4a1A4`1A4_5E45E45E45E4g00]J'`=aIMPNP4P41I4EP1POCNP21I48CNPPPQPQPTPZPQP5P6P6P71D4@R@,=R,3QPQP5P6P6P7PLEeFfC5PZPQPQPQP5P6P6P7P4PSg00VcR7PRCF,3QE\PZP41D4:R:=>4[=>4\P7AH4SX=>4@CF,3QC5PZPQ1=R:,3QPZPQ%2B#2#2#2#6RB#;1D4=R='=,3QPZPQ1K:Y,3QPZAH4XS/==,3QC5C5C5C5C5PUPWb2b3b4X04X:4X;4X<4W91JHF\Vg00^6\]A0E>;17C1/GF584[11BE14L<17FC/1L[[\H[[^04^:4^;4^<4^93P0142CP2f?f@P1PLP?PAPJP^O:b1bFbEbCbBbAb@b?bDb6DM%OF/1LRFeW8W7W5P0O1A01>;/9C/7C/18PDPKPLP2P1DMPFeX8HX7GW5P0O1n200100000021100010000W6X>4X=4P2P0O2X>4X=4o"). Qed.
(* [comment removed for export] *)
Lemma fits_pow2 k j : 17 <= k -> 0 <= j -> fits (2 ^ j) (2 ^ k) -> k < j.
Proof.
ltac2:(KReplay.run1 (kr_t_HeIface ()) [] "h02Hah14__x1h22H0h37__arithh44__ffh56__sat1h68__varmaph75__with84__p1h96__sat0h:6__sat3h;4__x2h<1Hh=2H1h>2H2h?2H3h@2H4hA6__sat2hB1ahC1qhD1rhE4__p2hF6__sat4hG4__x3hH4__x4hI1jhJ1khK1GhL3HabhM2HjhN2HkhO1LhP1bhQ1op;1p;2p;3p;4p;5p;7p;6p;8g0013j19Tg0026j1FTg001Xj1<Tg003Uj22Tg002[j21Tg00Wdj2dTg00;cj23Tg004Lj27Tg004ij2>Tg00abj2LTg00bJj3HTg005Fj1kTg005fj1jTg006Fj1iTg006dj1cTg007Bj1bTg007mj2YTg008Pj2`Tg0092j2_Tg009Lj2^Tg00:8j3=Tg00:Rj3]Tg00;1j4\Tg00<?j2GTg00=Aj2ATg00>kj1[Tg00bnj5STg00RNj4DTg00cUj2RTg00d4j2qTg00\QR0j2pTg00A?j2oTg00B0j2ZTg00BQj1nTg00Bjj26Tg00CJj2BTg00Cgj2WTg0041j2ETg00DNj2VTg00E5j2UTg00E[j2TTg00Y0j1OTg00YOj2KTg00Z8j3QTg00Zaj2hTg00[Mj3fTg00>Gj7eTg00HZj4JTg00[mj6gTg00?Mj3NTg00@0j3XTg000Oj7lTg00IEj8aTg00<]j6mTg00IiR1f0R2'2p=4%F2#Fp=@%92#9p=:f2R3f1R4'B/B2p=01312p=?g00JGR5/Y2p=;P5P4g00JeP2CJp=IP4g0000R6g00KLR7P7g00KlR8P2g00LLFlp=5P5P4g00LlP2CJp=Cf3R9P6P7P7P8P3P4P2Gap=8P4P6P7P7P8P2Emp=PA=521p=Mg00MSR:#9R;#9R<#9R=#F#<R>/24R?%44R@%<;RA/1311A9RB'dP0f4RC,1ARD%F:RE#@#@#@#@#@RF#9#@#:#<RG'3%F;RH#:#<RI%<FRF50D%9=#:#:#:#:R=#<RJ'7/>J/2Bf5RB/3CP211ABRK/3Gf6RL/3BRMPAP>PL1LALRN%?AROf7RP#4f8RQ,1ARR#?[[RS%4ARTg00dYRUf9RV=HA4UW0RW11AVRX#4\U^0TRYg00N8RZ#kR[%jZR\%i5R]%c5R^%b5R_1Y51R`%;A'I'51`_8RaP2P3g00NdRbg00ODRc'_1^23==bcdA]514C\Rcb4b6b7POP2b3Rbb9b5PNPSPWPYP[P\1G54RYP^P_%;>1A5:R:'C,5_RW%[7RSPWC8PaPcb4b6b7X1512>2P?[^15P2PVPPO2b3b9b5DS11A>11AL'21LAP%4Q%?X[\Of:R>=HA4VUX0T11A>R?#4\U^0Tp-0RWP[P\P5P]P4PYCDP^P_%9=#:#:#<R=#;1A5ERY'C,5_PSP_%;G,IY,5_PS1P_9C8C8PaPcb4b6b7X15W812=2134GP9[[^15^8WP2g00^6RGP?P9PCO4b3b5bAb2'RW<P2O1A0KIF/7J/>J/2D1qLB12BL,pMP013PL12LP13QPR0P2P2XO0P2O112PQ13VQPAPQPVA0XIFR0/oJRM%40%4Jf;R0,1ARD?0IF/7J#4[[RK1LAVR=%4>%?D[\ORDf<RN=HA4VUX0TRd11AN#4\U^0TRe1LANRNf=#4f>Rf,1ARg#?[\ORhf?Ri=HA4VUX0TRj11AiRi#4\U^0TRTA0gIF/ZJRg%MJRU#nRkA0iIFRi17iJ,>J16iJ'B5=5[Rl1WiJRi%?JRmf@,1A?0IFRn/6JRo#413oJ'E[Ro1VnJRn13J1RpfA,1A?0IFRq/6JRr,3J12r1'E[Rr1UqJRqfB,1A?0IFRs/7J#M\URt1TsJRsfCRu,1A?0IFRv/6J==5v\URw17vJRvP5fD,1A?0IF/6JRxP5P0P2PuO2XBORufE,1A#?^BOROPbb:bDbCb@b?b>b=b2b9b5bAb:bFPMPKP=PDPdPePNPhPjPTPgPlPiPoPnPrPqPtPsPwPvP5PxP5PuPOP[P\P51G53ROP4P]CDP^P_1A5;,C:,5_R:PSP:C8PaPcb4b6b7X15X;512241243[^15^;5P2fGfFPfO3b3b:bDbCb@b?b>b=b2b9b5bAb:bFDS12RXA02IF/7J/>J/241234A03IF/ZJA09IFRR17RJ,>J16RJ'B5=5\k1WRJA0CIFRR/6JRk#413kJ'E\m1VRJA0BIFRk/6JRf,3J12f1'E\p1UkJA0LIFRk/7J#M\U1TkJA0PIFRk/6J==5k\U17kJP5A0QIF/6JP5g00\kRk#ORp#ORf#O,K51K5f1K5p1K5k5Q55Q55Q5g00]J'h=fZ[P\P5P5POPC1G5CCDPCP51G59P4P]CDCDP^P_P_%;JR^,I`,5_PSP_P6P7P7P81P_L%9E,A5RE/I^,5_FeC8PSP_P_P_P6P7P7P8P5P^g00VcR8P`CJ,5_EgPSP51A5HRH%;I5N5%;F5N5P8AX5^Y=N5ECJ,5_C8PSP_1A5<R</CH,5_PSP_AX5Y^/C<,5_PS1P_PC8C8C8C8PaPcb4b6b7X15X;5XG5XH5X8WXEW13CJ,EB\mPG\U1>J3/BB9=5R[129C1>9J/2CPV[[[[^15^;5^G5^H5^8W^EWP2PGP@P4P>P0P3PLPPPQPVO:b3bDbCb@b?b>b=b2WLW<XP5XB5PXP?PCP2O4b2'RWKP2O1n200100000021000011000bQW<P2O1n200100000021100011000W2WMWNXI5XJ5P4P2O2XI5XJ5o"). Qed.

(* [comment removed for export] *)

Section IfaceR.
Variable L : heap_layout.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable HI : heap_iface.

Definition mallocR_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NREQ ->
    credit_okR cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debitR cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.

Definition alignedR_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 16 -> getr R 11%bv = Z_to_bv 64 n -> 0 < n <= NREQA ->
    credit_okR cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debitR cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_aligned_alloc L)) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
Definition freeR_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (A n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    In (A, n) LB ->
    getr R 10%bv = Z_to_bv 64 A ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        heap_pres L (lb_remove A LB) (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI (lb_remove A LB) (refundR cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.

Record heap_ifaceR_ok : Prop := HIROK {
  hir_malloc : mallocR_spec;
  hir_aligned : alignedR_spec;
  hir_free : freeR_spec;
  hir_free_null : free_null_spec L scfg;
  hir_frame : heap_frame L HI;
  hir_wf : heap_blocks_wf L HI;
  hir_perm : heap_perm HI
}.
End IfaceR.

(* [comment removed for export] *)
Section IfaceE.
Variable L : heap_layout.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.
Variable HI : heap_iface.
Variable lim : Z.

(* [comment removed for export] *)
Definition credit_okE (cr : credit) (n : Z) : Prop := 1 <= fst cr /\ (bm_on = true \/ cszR n <= snd cr).
Definition debitE (cr : credit) (n : Z) : credit := (fst cr - 1, Z.max 0 (snd cr - cszR n)).   (* [comment removed for export] *)

Definition mallocE_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NREQ ->
    credit_okE cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debitE cr n) M' (m_vmmaps model') ->
        fits lim n ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.

Definition alignedE_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 16 -> getr R 11%bv = Z_to_bv 64 n -> 0 < n <= NREQA ->
    credit_okE cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debitE cr n) M' (m_vmmaps model') ->
        fits lim n ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_aligned_alloc L)) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
Definition heap_fit : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (M : word -> option byte) (VM : VmMaps) (A n : Z),
    hi_heap HI LB cr M VM -> In (A, n) LB -> fits lim n.
Definition heap_limit : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (M : word -> option byte) (VM : VmMaps),
    hi_heap HI LB cr M VM -> vm_limit VM = lim.

Record heap_ifaceE_ok : Prop := HIEOK {
  hie_malloc : mallocE_spec;
  hie_aligned : alignedE_spec;
  hie_free : freeR_spec L scfg HI;
  hie_free_null : free_null_spec L scfg;
  hie_frame : heap_frame L HI;
  hie_wf : heap_blocks_wf L HI;
  hie_perm : heap_perm HI;
  hie_fit : heap_fit;
  hie_limit : heap_limit
}.

(* [comment removed for export] *)
Definition mallocF_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NREQ ->
    credit_okR cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debitR cr n) M' (m_vmmaps model') ->
        fits lim n ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.

Definition mallocS_spec : Prop :=
  bm_on = true ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NREQ ->
    1 <= fst cr ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (fst cr - 1, snd cr) M' (m_vmmaps model') ->
        fits lim n ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.

Definition freeS_spec : Prop :=
  bm_on = true ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (A n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    In (A, n) LB ->
    getr R 10%bv = Z_to_bv 64 A ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        heap_pres L (lb_remove A LB) (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI (lb_remove A LB) (fst cr + 1, snd cr) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.

Record heap_ifaceS_ok : Prop := HISOK {
  his_R : heap_ifaceR_ok L scfg HI;
  his_mallocF : mallocF_spec;
  his_mallocS : mallocS_spec;
  his_freeS : freeS_spec;
  his_fit : heap_fit;
  his_limit : heap_limit
}.
End IfaceE.

(* [comment removed for export] *)
