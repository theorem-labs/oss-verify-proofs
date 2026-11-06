(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_SumWalkTac () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib6Common8PropExec:bytes_le_NC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions>bv_swrap_smallC59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib6Common8PropExec4v_lwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib6Common8PropExec4c_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib6Common7CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common8PropExec7rdn_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof01".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_to_Z_4 : forall v : word, (bv_unsigned v < 2^32)%Z ->
  bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) [] "h02Hah14__p1h24__x1h31Hh42Hvh57__arithh64__ffh76__sat0h86__sat1h96__sat2h:6__sat3h;8__varmaph<5__with=1vh>1zp;1p;2p;3p;4p;6p;7p;8g0000j12Tg000Uj1@Tg0013j1ITg001Vj23Tg002@j15Tg002^j26Tg003;j21Tg003Wj14Tg0046j1FTg004Vj2ETg0053j2DTg005Sj3<Tg005mj1ATg006kj27Tg007Fj2?Tg007nj3=Tg008Rj1WTg0092j1VTg009Rj2UTg00:0j1TTg00:Nj1NTg00;9j2;Tg00;\j2HTg00<?j49Tg00<jj6GTg00=Nj1JTg00>0j3KTg00>Sj2CTg00?5j2LTg00?Oj2MTg00@;j3BTg00@Zj4OTg00ALj3PTg00Aoj2QTg00C7j1RTg00D4j2STg00E3j6\Tg00EQj2[Tg00Emj7ZTg00FQj7YTg00G5j8XTg00GYR0f0R1'[p=0f1R2g00H7R3g00HVR4P4g00I6R5P1g00IVFZp=:f2R6P3P4P4P5P2P1FYp=>f3R7P3P4P4P5P6P2P1GXp=8g00J6R8#2R9#2#2R:#2#2R;#2R<#@R=#I13=1%59R9%5;R>'6R?'1g00J[R@13=2RA%5:g00K9#4#4#4#4R:#F'E,69'D13=69<@1X>@%A2%0A%5<R<,69RB,1A'71?9>1109RC%0>110?[[%09RDg00KXREA=9>2UW0%0?\E^0D1?9<%0<110B[\CA=9<2VEX0D%0B\E^0Dp-0RDg00L4RE#W%VE1U@2%T@%N@REP@1;@0g00L`1H@8R8C9,:ER<PEP3P4P4P5P7EG5>E%J4R4PEP@P8g00MG1;@9%@;5K@C9,:ER;P4A>E<;C8C81CE5P1P6g00MnREg00NNR5'L1M16=<E5dAB@02COb6b;b<X2@W1%01/72112?%06116?'7[[^2@^1DP1f7,3=R=/1BP=f5f6O4b5b7b8b9b:b39PA?1Q:2#R1S:2E\W4W=o"). Qed.

Lemma v_lw_small : forall z, (0 <= z < 2147483648)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) [] "h04__x1h14__p1h27__arithh34__ffh48__varmaph55__with62Hah71zh82Hzh96__sat0h:6__sat1p;1p;2p;3p;4p;6p;8p;7g0000j10Tg002@j18Tg003;j22Tg006kj27Tg000Uj1=Tg0013j1HTg00Nnj1Ej2DTg001Vj2CTg00OTj2<Tg00?5j2?Tg005Sj3;Tg008Rj1ZTg0092j1VTg009Rj2UTg00:0j1TTg00:Nj1QTg00;9j29Tg00;\j2MTg00<?j45Tg00=Nj1GTg00P;j2FTg00>Sj2ITg00?Oj2JTg00@;j3KTg00@Zj4LTg00P^j1BTg00EQj2>Tg00Q;j3NTg00<jj6ATg007Fj2OTg002^j2PTg007nj3@Tg00>0j3RTg00Qhj3STg00E3j6]Tg00Rbj8\Tg00S?j1[Tg00Emj7YTg00FQj7WTg00G5j8XTg00GYR0f0R1'>p=3%01#0#0#0p=1f1R2g00H7R3g00HVR4P4g00I6R5P1g00IVFYp=4f2R6P3P4P4P5P2P1FWp=6f3R7P3P4P4P5P6P2P1GXp=:g00J[R8%31R9g00J6R:#0R;#1R<#0R=#0#1#1#1#1#1#1#8R>,21R?'7R@P8%==RA#HRB%EARCPC%=<R<1DA2RD,CARE'<P2PB\8/?CP8P21<<1=;86X78g00L4RC#ZRF%VCRC1U82RG%T8RH%Q8RIP81980g00L`RJ1M8:R:C5,4IRKP8P:g00MGRL198>RMC5,4IRN56I%G4ROP81F8MPJP:C5,4I=6INC:1II5RJP1P6g00MnRMg00NNRP'?1J16=;MPdAK802CLRPb3b4b5X08%B>/>2122>'7\@^08P1P6P2O2b29N<2PEp-0REPFPCPGPHPIPIP3P4P4P5P7EAR596IKPOPKC:PJPPb3b4b5X08W11792%32[^08^1EP1126>P6P2O3b2%8;R;%8=R='O120;%3=1P;=R6,20[[%3;R0g00KXR>A@;=2UW6%36\>^60PFPCPGPHPIA6I5NPOP8P:PL198;=R8AC5,4IC:PJPPb3b4b5X08X1E172?1226[^08^1EP1f4R1#3P1P7O3b2b9b:5S2E]G\%[D=;BDeW8W7o"). Qed.

(* [comment removed for export] *)
Lemma v_lw_m1 : v_lw (Z_to_bv 64 4294967295) = Z_to_bv 64 (-1).
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) [] "h02b1h12b2h21nh31Hp;1p;3p;2g0013j15Tg005Sj33Tg001Vj22Tg00T8j38Tg0000j14Tg000Uj1<Tg00T\j10Tg002@j16Tg00Nnj27Tg00S?j19Tg00UAj1>Tg00?5j2=Tf0R0#0#0p=;%00#0#0#0p=:%00#0#0#0#0#0#0#0p=1g00U_R1%50R2f1R3#5R4g006kf2R5#5?330g00J[R6f3R7/25127333R8[12531250536%57?353[R9f4#5?375\8A8530P0n2001000000120000000W1W0W2P9^14^02^21P0g00J6R0#4#4#4#4#4#4#<R1%00#;#:#1#1#1R2#6,71#9R4%>0,71R0%12#1#1#1#6,=612141210536dO4b3o"). Qed.

Lemma c_eq_Z : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) [] "h07__arithh14__p1h26__sat0h36__sat1h44__x1h52Hah64__ffh78__varmaph85__with91zh:2Hbh;1ah<1bp;1p;2p;3p;4p;6p;7p;8g0000j12Tg002@j1<Tg002^j2DTg003;j21Tg006kj25Tg000Uj1LTg00Nnj28Tg001Vj2?Tg00V=j23Tg005Sj34Tg00?5j2@Tg007Fj2ATg007nj3VTg008Rj1UTg0092j1TTg009Rj2OTg00:0j1NTg00:Nj1MTg00;9j2=Tg00;\j2KTg00<?j46Tg00<jj6GTg00=Nj1FTg00>Sj2HTg00?Oj2ETg00@;j3ITg00@Zj4JTg00>0j3CTg00Qhj37Tg00E3j6>Tg00VZj2BTg00EQj2PTg00Emj7QTg00FQj7RTg00G5j8STg00GYR0f0R1'Pp=0f1R2g00H7R3g00HVR4P4g00I6R5P1g00IVFQp=;f2R6P3P4P4P5P2P1FRp=:f3R7P3P4P4P5P6P2P1GSp=9g00J[R8%02R9g00J6R:#2R;#<R<%2;#2#2#2#2R;#<R='DR>,12R?'5R@P8P7g00MnRA%L;R;18;7RB'?RC,31f4RD/37RE34X98P8P613D1=4AEX981376RE,@A18;6RF,?;1A<=RG110<%0=110>[[RH%0<RIg00KXRJAV<=2UW5R=%0>\J^5IRIp-0RJg00L4RK#URL%TKRK1O82RM%N8RN%M8ROP81=80g00L`1K8:R:C6,;ORPPOP3P4P4P5P7EGR35:O%F4R4PPC91HO5R5P1P6g00NNRP,@A1E16=4APdAI802CJR0b6b7b8X48W1RP%01/52P9[^48^1JR9P1f5RQ/1>PQP7O3b0b2b3PGPHP=PIPLPKPMPNPOP8P:g00MG1=8<=C8;C6,;OR;9:O3P4P;C9P5P0b6b7b8X48X1JR0111>,52P?[^48^1JRJP1%0QPQP7O3b0b2b3576E>PCPGPHP=PIPPP9P1f6R9/1>P9PDO3b0b2b3PGPHP=PIP0PJP1%09P9PDO3b0b2b3577E>1BBF=4AEeX:@W5X<8W;o"). Qed.

Lemma c_eq_refl : forall x : word, c_eq x x = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) [] "h01xp;1p;2p;3g0000j10Tg000Uj15Tg0013j12Tg00WSj21Tg00VZj24Tg005Sj33Tg00J6#0#0#0#0#0#0#5R0#2f0R1,10g00Mn1411g00NN33eW0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zlen :=
  repeat match goal with
         | |- context [length (word_to_le_bytes ?n ?v)] => rewrite (length_N_to_le_bytes n v)
         end;
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ length].
Ltac zsimp := zlen; u_norm.

(* [comment removed for export] *)
Ltac sok_stack SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 144%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac lia_fast := first [ solve [ clear_disj; lia ] | lia ].
(* [comment removed for export] *)
Lemma rdn_wbytes_out_Z : forall segs bs m (zb za : Z) n,
  (0 <= za < 2^64 /\ za + Z.of_nat n <= 2^64 /\ 0 <= zb < 2^64 /\
   zb + Z.of_nat (length bs) <= 2^64 /\
   (za + Z.of_nat n <= zb \/ zb + Z.of_nat (length bs) <= za))%Z ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) [] "h04__x1h17__arithh26__sat1h36__sat2h44cstrh55cstr0h61Hh74__ffh84__p1h98__varmaph:5__with;4__x2h<1zh=2Hah>4__x3h?4__x4h@3HanhA2HbhB3HbnhC2HdhD2bshE1mhF1nhG4segshH2zahI2zbp;1p;2p;3p;4p;7p;6p;9p;8g0092j1MTg0000j1=Tg000Uj1QTg0013j1OTg00XSj1XTg002@j1STg002^j2`Tg003;j2;Tg006kR0j29Tg00EQj20Tg00Nnj21Tg00Y5j3FTg00Yoj46Tg005Sj3?Tg0046j1:Tg00Zgj24Tg001Vj2LTg00[Dj2KTg00[dj1PTg007Fj2_Tg007nj3^Tg008Rj1]Tg009Rj2ATg00\Ij1\Tg00\gj4JTg00:0j1[Tg00:Nj1ZTg00;\j2ETg00]Ej3NTg00T\j1YTg00]hj7oTg00=Nj1nTg00>Sj2mTg00?5j2lTg00?Oj2kTg00@;j3hTg00@Zj4gTg00;9j2VTg00<jj6fTg00>0j3dTg00<?j4RTg00Qhj3UTg00E3j6GTg00^Ll9bTg00_Nj2WTg00Emj7aTg00G5j8iTg00FQj7jTg00GYR1f0R2'0p=5f1R3%:2'4p=2f2R4,011;32'9p=81K32#:,44p=7f3R5/041032'Wp=31932,94p=<1043/92p=B1443/02p=>1K32#:p=D1043/W2p=Cg00J[R6P3g00L`P2CRp=IP3g00H7R7g00HVR8P8g00I6R9P2g00IVFap=@P5P7P8P8P9P4P3P2Gip=HP4P7P8P8P9P3P2Fjp=T1013/92p=e1;32,94p=cg00_h#Mg00J6R:#=R;#=R<#=R=#Q#OR>#MR?%==#=#=R=#QR@#O%X>[g00`g%53RA%S;RB%S=R='`RC,;3RD'91232RE/0CA844CRFf4RG974>RH/0CPEP4PHP3C33<3<P0PF1243RFA855Cf5RH975>RE/0CPFP5PEP4C33<7BC%X?R?f7RE11@Gf6RF5FH11@5RIP4C6PEPHPIP4C63?P2A8GGC12HGRIA8FFCf8RJ97F>RK/0CPIPFPKPHC33<7BCP012FHRK/0CA8EECf9RI97E>RL/0CPKPEPLPFC33<f;RL11@Jf:RK5FI11@ERMPFC6PLPIPMPFC65??P2%:E=>JCA8KKCf<RE97K>RM/0C12IJPKPMPIC33<P0A8LLCf=RM97L>RJ12KIPLPJPKC37BCf?RJ11@Ef>RI5FM11@LRLPKC6PJPMPLPKC65??P2A8MMCf@RL97I>RN12MEPIPNPMC37BCP0fAR097J>RN/0C12IMPJPNPIC3fCRN11@LfBRM5F011@JRJPIC6PNP0PJPIC65??P21D>N=>0C120LfDRL,D>=>M07CMfFR?fERJPL11@NRE11@MROP0P6PM%:MR0,42RP11@L,L@RL1D>?RQ=>L23CX<6P6PN14N0P2142QRQPNC3X<61K>JRJ#PRL%:J#5RJ%PMRR%50R01_B=RS1;1B%5=1;1C[[RT%5BRUg00KXRVA^B=3UW=R=%5C\V^=URUg00L4RV#]RW%MVRVP6P61A6GP4%\6RXCJP31A65CJ%[6RY%Z6RZPZP7P8P8P91E6:R[1E6;5N6R;%Y:,E6R:'I,@Z1E6<9N6:/I[,@ZFoR:%n8R<P:CH1mZ9R:P2P4g00MnR\g00NNR]'l1k24=?\]dAh613CgR]b7b9b:X06X;6X>6X?61423R\A>4527C41434R^A>5G37C5[^06^;6^>6^?6P2fJ,D>R>fHRG%:?R?fGR_PHO5b1b2b3b5b41L@EREPLPJPRP0PSPTP=PUp-0RHPWPV1A63R`PYPZ1V61/I[,@ZR1PZP7P8P8P9P5EfR55TZP<P1CHP:P]b7b9b:X06W8R11e23PA[^06^8HRAP21;GCPGPKO3b1b2b3b5b4PLPJPRP0PSPTP=PUPWPVP`PYPZP6P[g00MG1V6B=d6@RBCR,@ZR[9TZ5P<P[CHP:P]b7b9b:X06X8HR[Ac32CPD[^06^8HRHP2%5GPGPKO3b1b2b3b5b45UNRKEG1L@OROPLPJPRP0PSPTP=PUP1PAP21;_CP_PMO3b1b2b3b5b4PLPJPRP0PSPTP=PUP[PHP2%5_P_PMO3b1b2b3b5b45UMRHEGP6PM10PCX<6PLPJPRP0PSPTP=PUPWPVP61A64P3PXCJPYPZ1I;B,@ZRZP<PZCHP:P]b7b9b:X06X;6R]10\C10^C[^06^;6R^P2P?P_PIO3b1b2b3b5b4POPHEGP6PN10QCX<6PLPJPRP0PSPTP=PUP]P^P2P>PGPFO3b1b2b3b5b4PEPKEGM9bWCWBP3P2O2n2001000000121000000W6WAP3P2O2n2001000000121000000W6W@P3P2O2n2001000000121000000W6W=P3P2O2n2001000000121000000W6WFXH6XI6WEWDWGo"). Qed.
Ltac rdn_peel1 :=
  first [ rewrite rdn_wbytes_out_Z by (zlen; lia_fast)
        | rewrite rdn_wbytes_out by (zsimp; lia_fast) ].  (* [comment removed for export] *)
Ltac rdn_by H := repeat rdn_peel1; exact H.
(* [comment removed for export] *)
Ltac rdn_hyp :=
  match goal with
  | H : rdn _ _ ?a ?n = Some _ |- rdn _ _ ?a ?n = Some _ => exact H
  end.
Ltac rdn_solve :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (rdn_peel1; rdn_solve)
  | |- _ => rdn_hyp
  end.

(* [comment removed for export] *)
Ltac zbv_target x i :=
  lazymatch x with
  | Z_to_bv 64 (?a - ?b)%Z => let d := eval cbv in (b - i)%Z in constr:(Z_to_bv 64 (a - d))
  | Z_to_bv 64 (?a + ?b)%Z => let d := eval cbv in (b + i)%Z in constr:(Z_to_bv 64 (a + d))
  | Z_to_bv 64 ?a =>
      lazymatch i with
      | Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (a - d))
      | _ => constr:(Z_to_bv 64 (a + i))
      end
  | _ =>
      lazymatch i with
      | Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (bv_unsigned x - d))
      | _ => constr:(Z_to_bv 64 (bv_unsigned x + i))
      end
  end.

(* [comment removed for export] *)
Ltac addr_norm :=
  match goal with
  | |- context [v_addi ?x ?i] =>
      let e := constr:(v_addi x i) in
      tryif check_closed_term e then wlit_closed e
      else first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac sp_renorm :=
  match goal with
  | |- context [regupd _ 2 (v_addi ?x ?i)] =>
      let e := constr:(v_addi x i) in
      first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  end.

(* [comment removed for export] *)
Ltac getr_hyps :=
  repeat match goal with
         | H : getr ?rs ?n = _ |- context [getr ?rs ?n] => rewrite H
         end.
Ltac addr_tac := getr_hyps; unfold v_addi; u_norm; first [reflexivity | f_equal; lia | apply bv_eq; u_norm; lia].
Ltac val_tac := first [reflexivity | assumption | symmetry; assumption].

(* [comment removed for export] *)
Ltac stepST F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac
        | reflexivity | oktac ]
    end
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepLD F D bsv vv rdtac vtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac | vtac ]
  | step_simpl ]; vnorm.

(* [comment removed for export] *)
Ltac stepLD8 F D vv := stepLD F D (word_to_le_bytes 8 vv) vv ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).

(* [comment removed for export] *)
Ltac stepLBU F D bb rdtac :=
  chain_step;
  [ reflexivity
  | eapply step_lbu with (b := bb);
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac ]
  | step_simpl ]; vnorm.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (u_Z2bv z) by lia
      end
  end.

(* [comment removed for export] *)
Ltac addi_renorm :=
  match goal with
  | |- context [regupd _ _ (v_addi (Z_to_bv 64 ?x) ?i)] =>
      let t := zbv_target (Z_to_bv 64 x) i in
      replace (v_addi (Z_to_bv 64 x) i) with t by (unfold v_addi; unorm; f_equal; lia)
  end.


Lemma rdn_img : forall segs mem (a : Z) (n : nat) (lo hi : Z),
  (forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
  (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z -> (0 <= lo)%Z -> (hi < 2^64)%Z ->
  rdn segs mem (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) [] "h04__x1h14__x2h27__arithh37__sat65h47__sat66h54__x3h64cstrh74__ffh88__varmaph95__with:2Hxh;1xh<2Hah=4__x4h>4__x5h?1zh@2H0hA3H64hB3HhihC4HimghD3HlohE1ahF2hihG1ihH2lohI3memhJ1nhK4segsp;1p;2p;3p;4p;6p;7p;8g0092j1RTg0000j1;Tg000Uj1KTg0013j1ITg00XSj1iTg00EQj20Tg003;j22Tg006kj29Tg00Nnj2<Tg00=Nj1JTg005Sj3CTg0046j17Tg00Zgj24Tg002@j1PTg002^j2cTg00[dj1GTg007Fj2[Tg007nj3ZTg003Wj1BTg00aFj2=Tg00aoj2ATg008Rj1YTg00b[j3@Tg009Rj2?Tg00\Ij1XTg00:0j1WTg00:Nj1VTg00;\j2>Tg00;9j2HTg00>0j3TTg00]Ej3FTg00>Sj2STg00?5j2UTg00?Oj2hTg00@;j3gTg00@Zj4fTg001Vj28Tg00T\j1MTg00Qhj3LTg00E3j6bj7\Tg00c;j2aTg00cmj6]Tg00dIj7^Tg00eEj3_Tg00\gj4`Tg00<?j4OTg00Emj7QTg00G5j8dTg00FQj7eTg00GYR0f0R1'0p=5g00J[R2f1R3;_1p=:P2f2R4P3P1C`p=6P2P3g00MGP1COp=DP3g00H7R5g00HVR6P6g00I6R7P1g00IVR8FQp=EP4P5P6P6P7P2P3g00L`P1COP8FQp=1f3R8P5P6P6P7P4P3P1Gdp=3P4P5P6P6P7P3P1Fep=Ng00_h#Rg00J6R5#;R9#;R:#;R;#;#;#;R<#KR=#IR>%K;#IR;#iR?];g00`g10411213'9f6R@1<=3O1%J;R;5C?[^G2f4RA,04f5RB%7A'4/04%5A%P9RC%P<R<'cRD,2Af:REf7RFf9RGP;V>f8RH,<=RIP2PH%7HRJ,41/0DX?2%GFRK%7F#5RL1[C<RM120C%5<120D[[RN%5CROg00KXRPAZC<3UW<R<%5D\P^<OROg00L4RPg00K9RQ#BRR#BRS,=2RT1=2R1=2QRQ':RR':RUg00enRV'A%YPRW3@RX%RPRY1?28RZ%X2R[764?63[%W2R\%V2R]1>2:R:1H2C=T2=RC'D,E]R^%J6R6P]1>25R_1>29R`5F2Ra=1]:P6A1]aCC3C31S]7R7P1P4g00MnRag00NNRb'U1h14=CabdAg203CfRbb7b8b9X02X12X52124D1434/081448Ra/0D[[^02^12^52P1PGf;Rc#7Rdf<RePAP@O5b2b3b4b618=IPKPLPMPNP<POPXPY1?24RX?63[P\P]1H20R0=1]`P6P]A1]`_P6A1]0_C3C3P7Pbb7b8b9X02X12RI%53Rf1043%54[[^02^12RgP1PEPePBPFO4b2b3b4b6PKPLPMPNP<PO%BSRS,=2RL/:U/AV=@PWPYA6Z8[?63XP\P]%M5,>2R591]0P6P]P^P6P]AF2_5=1]:P61D_C,E]C3C3C3P7Pbb7b8b9X02X12X52RC128DRD10aAPD[[\f^02^12^52RfP1PGPdPeP8PAP@O6b2b3b4b65LHEb1<=G,8=Rd18=1RD'014dJ,2D'9P2PE18=4RD,01%7ERd,41,2D'9f=RJP8O1=C?;]:X?218=3Ra,0E%7GR^,4E,2a'9P>1<=DPJP1O1=C?;X;>PFPD%GE%5dPMPNP<PO1:TQ,:L/AV%BS,=2/:R/AV=@PW5@PPY1?2A?64[1?2B?68[763P\P]A1]:`%M9,>29F2:R9,D`,E]5N]P6P]A1]95P6P]A1]_:P6A1]_`1D`5,E]5N]C3C3C3P7Pbb7b8b9X02X12X52X=2X>21083148A,23'914AB/08104B108A12AB'9[[[^02^12^52^=2^>2P1f>RB#7f?Pe18=@PJPAPGPEO8b2b3b4b6O2P41a=4E]W:1<=E,8=%GGR=%5^R^PMPNP<POPIPgP1PePBPFPGO4b2b3b4b6P=P^PMPNP<POPCPfP1Pc%7JPBP8P@PHO6b2b3b4b65LEP1F\W:X;>F^WAW@WBWDWCXF2XH2WJXE2WIWKo"). Qed.

(* [comment removed for export] *)
Ltac img_exists :=
  lazymatch goal with |- exists bs, ?l = Some bs =>
    let v := eval vm_compute in l in
    lazymatch v with Some ?bs => exists bs; vm_compute; reflexivity end
  end.

(* [comment removed for export] *)
Ltac enum_nat k N tac :=
  let rec go n := lazymatch n with
    | O => lia
    | S ?m => destruct k as [|k]; [tac | go m]
    end in go N.


(* [comment removed for export] *)
Ltac zaddr H :=
  repeat match type of H with
  | context [Z_to_bv 64 (?a + ?b)%Z] =>
      let c := eval cbv in (a + b)%Z in change (a + b)%Z with c in H
  end.

(* [comment removed for export] *)
Ltac zaddr_goal :=
  repeat match goal with
  | |- context [Z_to_bv 64 (?a + ?b)%Z] =>
      let c := eval cbv in (a + b)%Z in
      lazymatch c with
      | Zpos _ => change (a + b)%Z with c
      end
  end.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
