(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import MState Mem Cells ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanHandoff.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanPlan MainExport MainFactsAsan.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg ABase AMalloc_iface ARepInit_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AResv () := "C46Stdlib5Lists4List2InC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K59OSSVerify5KrLib2AS:MainExport4zexp01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport6lentry01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec;AsanHandoff7resv_ofC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib2AS:MainExport2zvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2or00C46Stdlib5Lists4List:in_app_iffI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC59OSSVerify5KrLib4Spec;AsanHandoff5iv_ofC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init5Logic2eq01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List;in_flat_mapK47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib5Lists4List7map_appK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib5AsanW=AMalloc_iface4pcovC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06I59OSSVerify5KrLib2AS:MainExport6lentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=MainFactsAsan;asan_ledgerC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00I69OSSVerify5KrLib2AS8AsanPlan2AP5mkind00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec;AsanHandoff4uns2C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic2or02C47Corelib4Init5Logic6eq_indC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic7and_indK46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib5AsanW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;AsanHandoff=reserved_evalC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib2AS:MainExport8pfact_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00K59OSSVerify5KrLib2AS:MainExport5pfact01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;AsanHandoff:pfact_findC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW5AResv8resv_imgC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport6lentry02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c59OSSVerify5KrLib5AsanW5AResv8resv_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib5AsanW5AResv:resv_namedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<ARepInit_kit2LVC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase7alayout01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface8aresv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;AsanHandoff9pfact_eqbC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC59OSSVerify5KrLib5AsanW5ABase4al_VC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS:MainExport5pfact00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=MainFactsAsan?asan_pure_factsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP5mkind01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP5mkind02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP5mkind04C1?~~~~~~~~~~~~~~~".
Import ListNotations. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma resv_named : forall V k n kd lo hi,
  In (LMap (ZMul (ZLit 4096) (ZV k)) n kd) asan_ledger ->
  0 <= V k <= 34359738368 -> 0 <= n < 2^62 ->
  4096 * V k <= lo -> hi <= 4096 * V k + n ->
  pcov (resv_of V) lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_AResv ()) ["CANSEC1"] "p'0h01xh11lh21Ah34__x1h41Bh51ei001eh61fh71yh81Hh97__arithh:4__ffh;8__varmaph<5__with=4__x2h>4__x3h?4__x4h@4__x5hA1ahB2l'hC1zhD2HIhE3HINhF2HNhG2HVhH2HxhI2LOhJ1VhK2hihL2ivhM1ki011khN2kdhO2lohP1ni021ni031bp&0p;1p;2p;3p;4p;5p;6p;7p;8p-1g0000R0p4p710p8g000GR1p4p7210R2g000dR3p4p710p8g001Bj15Tg001gj1ETg002Ek107Tg003>j1QTg0047j2RTg0050j3eTg005kj27Tg006Gj1HTg006lj2_Tg007Ij29Tg007fj24Tg008Cj2jTg008cj1[TP0j30Tg009`j3YTg00:=j3WTg00:ZR0j23Tg00;5j1CTg00;Uj1bTg00<3j1uTg00<Vj2?Tg00=Kj12Tg00>:j48Tg00>Zj1aTg00?:j36Tg00?Zj4=Tg00@6j1nTg00A4j3DTg00AQj2`Tg00Akj4mTg00BJj3:Tg00Bdj2LTg00C>j5lTg00C]R4j1kTg00DXj2TTg00E>j2KTg00Ehj2^Tg00FBj2]Tg00F`k106Tg00G>k105Tg00Gij2STg00HLj2JTg00Hoj3iTg00IRk104Tg00J4k203Tg00JVk202Tg00KBk300Tg00Kaj4~Tg00LSj2fTP3j6UTg00MOj2{Tg00N8j1MTg00NWj2GTg00O@j3zTg00Oij2OTg00PUj2xTg00QAj3wTg00QdR3j4PTg00RAj5vTg00Raj3dTg00S;j4\Tg00SVj4ZTg00T0j5tTg00TLj1yTg00Tjj4VTg00UHj3sTg00Ukj3|Tg00Vhj2gTg00WDj4hTg00Woj7rTg00XSk701Tg00Y7j8qTg00Y[j3pTf0R5#5#5#5#5p=@%55#5p=cg00ZDR6g00[?R7705p=Xf2R8f1R9'7/35p=of3R:/781g95'3p=;g00\@R;P;P9P5C8p=>P6P9P5P7CPp=NP;P9g00\^P5Chp=<P9g00]ER<g00]dR=P=g00^DR>P5g00^dFrp=1P;P9g00_DP5Chp=FP8P<P=P=P>P9P5K01p=BP:P<P=P=P>P8P9P5Gqp=I1g95,38p=}Ap;95p=Ag00_kR<P;]0g00`Jg00aER?#5R@#5RA#@RB#c#@RC#ERD$07REf4RF#Q'R?e:8#Xg00ajRGf6RHf5RIO1RJ%5C#c#@#@#@#@#@#ERC,7J3oPGPIPI%E@RJ%H?RK#H#H#H#5RL#E'_RMC;f8RNf7ROO1,9D/7Ff9RPPNO1,9D/4O,7FPOP5P5PHC;1j;;RQf=RR#[90Q5AY;;5P8P8AW;;5C;'3XLQf<RSf;RTO1,9DRUf:RV,4U'>RU%[S90QURWAY;;UP9P9AW;;UC;RU%CQRX%bBRY#uRZ/jZR[PQP4P6%C[R\P5PZPZf@R]/?8#2%29R^C8%a[R_56[P_n0110000023010310210110102X56,N[R`C=P[PQP4g00bH#nRaC=Rb5DQPRPSO1Rc,9DRd14dT'>Rd=0Q5X1Xg00c=p4p710RX%C5Re%C9RfP0AD:8990:5A0F9:A0F98'`Rg[A0:58A0:59'`ADF:890F9[RhADIF:90I8\gP:P8P9P5CmP5n2001000000120000000XA8WBW1W2Ph^A8^Bf^1e^2XP5PQP[PQP4P6P\P5PZPZfA/?8#2P^C8=6[_P_n0110000023010310210110102X56,N[C=RXPbPdA0QdXA0QdbP1p4p710R1P9\9Rd%C8RbP0PFP:P8P9C=90:5PFP5O1RX=:I8A0H5:Re'3X0I,LIRh[P:P5O1Rg=:F9A0I58Ri'3X0F,LFPIPFP:P8C=90F9[RjPHPIPFP:C=90I8\hPFP:P8P9P5DlP5n2001000000120000000X78W1W6X42W2Pj^78^1b^6d^42^21P5P[PQP4P6P\P5PZPZfB/?8#2P^C8=6[_P_n0110000023010310210110102X56,N[R1f>R2PRO1,9DRd14dS'>RjP[%k5f?RhP2O1Rk,9DRl14lR'>Rm5:QP6P\P5PZPZfC/?8#2P^C8=6[_P_n0110000023010310210110102R^X56R\,N[90[5'3X0[PZPZ%QR,RE,?2Rn#2%2SC8Ro%ko=:QjRpA0[o1P;Pd1TYR,KY,45,>5=:QmXC;P;PS14l5,>l=:QmXC;1^Qj1TYSRm,KYg00cZRl#aRo%ClR11];9Rq&06;Rr&05;Rs1S;GRt1J;?R?'<,1sRu1S;JRv%bL5i;,F?,1s5Bs&04=R=Ai;vYRv,F?,1s9BsuCI203s>R>P5P8g00dFRLg00dfRw'^20258=:LwdB00;G9C~Rwb:b;b<X3;17G5RL?}5MPGP9P9%EB,_JRJC;[^3;P5PRPOO2b9,fSEU1TYd,KY1{;Dg00eFRO#MRB,G;RM5z;1G;ORO'Ag00eeRx'O%MBRB#MRy,G;Rz,AO/Ox,xO=6lo56lP1PqPrPs1S;C,<?,1s9BsuP=1S;D=w;?R?,<t,1s1F?v,1s5BsCIP>Pwb:b;b<X3;175C,3LPG19D9RGPGPJC;[^3;P5PkPNO2b9,fdEUPZPZ1TYnPmC8Rm9YZZ,KYRnAWZZm,KY,4n'>=:QjePpeP3p4p710RpP3p4p7210R3Pf\9RfP0PFP:P8P9CP90:5A0I8X,3eX0I,LIRe[A0F9g,3iX0F,LFPIPFP:P8CP90F9[RiPHPIPFP:CP90I8\ePFP:P8P9P5DvP5n2001000000120000000X78X1bW6W4W2Pi^78^1b^6f^43^2pP5P6P[P\P7PZPZ%Q2,RER7,?h#2%2RC8R\P6%X5PZPZ%Qh,RE,?]#2%22C8=0[^'3X06Ae7RSR7%X7A6[\_90[\PPA:[\\A0[\_1^[\3dC\CZO6b8C\CZO6b83dO5b8P[PQP4AD[`aC=P[PQP4P`PaDtEUPWe1G;B/AO,Az/Ox%My,G;1AMO'A/Ox=6lo56lP1P;P;1];FP8%y;R1CVP9P;1];IP:P1CVCVPrPs1J;ARA1J;@Rr'<,1s%H@,J;R@,Fr,1s5BsP=Ps1J;K9s;?RK,<@,1sP=Ps1<?A,1sP=1<?r,1s1FrK,1s5BsCICICIP>Pwb:b;b<X3;X=;X>;X?;X@;P:P9P9PFC;14G:,7I19D8/7I19D:RDPFPF14DIC;[[[^3;^=;^>;^?;^@;P5PNPPPTP8PcP9P:PFO8b9PUeC\CZWHX0;%[V?|HIeWDWIWFWGWEXK;XO;WNXP;XM<WJo"). Qed.

(* [comment removed for export] *)
Lemma resv_lit : forall V b n kd lo hi,
  In (LMap (ZLit b) n kd) asan_ledger ->
  0 <= b < 2^62 -> 0 <= n < 2^62 ->
  b <= lo -> hi <= b + n ->
  pcov (resv_of V) lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_AResv ()) ["CANSEC1"] "p'0h01lh11xh21Ah31Bh44__x1h51ei001eh61fh71yh81Hh97__arithh:4__ffh;8__varmaph<5__with=4__x2h>4__x3h?4__x4h@4__x5hA1ahB2l'hC1zhD2HBhE2HIhF3HINhG2HNhH2HxhI2LOhJ1VhK1bi011bhL2hihM2ivhN2kdhO2lohP1ni021ni031kp;1p;3p;2p;4p;5p;6p;7p;8g002Ej1MTg0050j3dTg001Bj18Tg001gj1XTg006Gj1ATg006lj2_Tg005kj2BTg007fj22Tg008Cj2[Tg008cj1PTg0000j30Tg009`j3YTg00:=j3WTg00:ZR0j26Tg00;5j1=Tg00;Uj1`Tg00<3j1qTg00<Vj2;Tg00=Kj11Tg00>:j44Tg00>Zj1aTg00?:j3<Tg00?Zj49Tg00@6j1jTg00A4j3>Tg00AQj2\Tg00Akj4iTg00BJj33Tg00Bdj2ETg00C>j5hTg00C]R1j1ZTg00DXj2OTg00E>j2FTg00Ehj2NTg00FBj2TTg00F`j1gTg00G>j1zTg00Gij2fTg00HLj2CTg00Hoj3eTg00IRj1yTg00J4j2xTg00JVj2wTg00KBj3uTg00Kaj4tTg00LSj2cTg000dj6VTg00QdR2j4DTg00RAj5rTg00Raj3^Tg00S;j4QTg00SVj4RTg00T0j5pTg00N8j1ITg00NWj2?Tg00Y[j3HTg00Oij2]Tg00TLj1oTg00Tjj4UTg00UHj3nTg00Ukj3mTg00Vhj2lTg00WDj4bTg00Woj7sTg00XSj7kTg00Y7j8vTg00ZDR3f0R4g00[?R530p=Sf3R6f2R7'Bf1R8/l4'6p=7g00\@R9P9P8P4C4p=:P3P8P4P5CDp=GP9P8g00\^P4Cbp=@P8g00]ER:g00]dR;P;g00^DR<P4g00^dFsp=5P9P8g00_DP4Cbp=LP7P:P;P;P<P8P4Fkp=JP6P:P;P;P<P7P8P4Gvp=Kg00_kP9[g00`Jf4R:#M?d67#Sg00ajR=f5R>P>g00aER?#8R@#XRA%A?RB#A#A#A#8RC#X'_RDC7REf7RF/B:f8RG/2F,B:PFP4P4f6RHC71[99RIf=RJ#P90I4AY994P7P7AW994C7'6XMIf;RKf:RL,2K':RMf<RN#P90IMROAY99MP8P8AW99MC7RM%=IRP%8@RQ#8#8#8#8RR#`RS#qRT/[TRUPIP1P3%=URVP4PTPTf@RW/;7#1%18RXC4%aURY5<UPYn0110000023010110210310102X53,GURZC9PUPIP1g00bH#jR[C9R\5>I12NK,:NR]=0I4X0Pg00c=p4p710RP%=4R^%=8R_P0A>6789064A0:86A0:87'\R`[A0647A0648'\A>:6790:8[RaA>>:690>7\`P6P7P8P4CiP4n2001000000120000000XA7WBW0W2Pa^A7^B_^0^^2PP4PIPUPIP1P3PVP4PTPTfA/;7#1PXC4=<UYPYn0110000023010110210310102X53,GUC9RPP\P]A0I]PA0I]\g000GR]p4p710R\P]p4p7210R]P8\8RP%=7R^P0P:P6P7P8C99064P:P4O1Ra=3>7A0H46R`'6X1>,E>Rb[P6P4O1Rc=3:8A0>47Rd'6X1:,E:P>P:P6P7C990:8[RePHP>P:P6C990>7\bP:P6P7P8P4DhP4n2001000000120000000X77W0W6W3W2Pe^77^0^^6P^3]^2\P4PUPIP1P3PVP4PTPTfB/;7#1PXC4=<UYPYn0110000023010110210310102X53,GUR\12JN,:JR]PU%Z4f>RP12PJ':Re53IP3PVP4PTPTfC/;7#1PXC4=<UYPYn0110000023010110210310102RXX53RV,GU90U4'6X1UPTPT%MJ,;PRb#1%1NC4Rf%Zf=3I]RgA0Uf\P9PJ1OSJ,FSRf,24,:4=3IeXC9P9PN12P4,:P=3IeXC91NI]1OSNRe,FSg00cZR\#aRh%=\Ri1T98%g9Rj%z9Rk1f9=1C9?R?'@,5kRl1f9ARm%`C5e9,L?,5k5Jk%y;R;Ae9mS,L?,5k9JklCK1xk<R<P4P7g00dFRlg00dfRm'N1w47=3lmdAu9=8CtRmb:b;b<X49RlP=P4P4PDC7P=P8P8%XR,_AC7[^49RAP4PJPFO2b9,cNEVPfPlPAP4PPPGO2b9,cJEVPTPT1OSbPeC4Re9YTT,FSRbAWTTe,FS,2b':=3I]ePgeP2p4p710RgP2p4p7210R2P_\8R_P0P:P6P7P8CD9064A0>7a,6`X1>,E>R`[A0:8c,6dX1:,E:P>P:P6P7CD90:8[RdPHP>P:P6CD90>7\`P:P6P7P8P4DrP4n2001000000120000000X77X0^W6W3W2Pd^77^0^^6_^32^2gP4P3PUPVP5PTPTf?R5%MPRV';#1%1JC4RgP3%S4PTPT%M5,;W#1%1PC4=0UX'6X13AdVJNRV%SVA<UgY90Ugf9RVA3UggA0UgY1NUg3^CQCRO6b8CQCRO6b83^O5b8PUPIP1A>UZ[C9PUPIP1PZP[DpEVPOeg00eFRO#IR[#IRZ#IR1,?91?9Z1?9ORO5H95H9g00eeRZ']%I1,?91?9[=H9O5H9/]Z=<\h5<\PiP9P91T9:P7%o9RiCUP8P91T9>P6PiCUCUPjPk1C9QRQ1C9@Rj'@,5k%A@,C9R@,Lj,5k5JkP;Pk1C9B9n9?RB,@@,5kP;Pk1@?Q,5kP;1@?j,5k1LjB,5k5JkCKCKCKP<Pmb:b;b<X49X=9X>9X?9X@9P6P8P8P:C71286,B>1B7>P6P:P:126>C7[[[^49^=9^>9^?9^@9P4PGPVPKP7PNP8P6P:O8b9PMeCQCRWHX19%PL?mH>eWEWIXGEWDWFXL9XO9WNXP9XK9WJo"). Qed.

(* [comment removed for export] *)
Lemma resv_img : forall V, pcov (resv_of V) 0x10000 AIMG_HI.
Proof.
  intros V x Hx. unfold AIMG_HI in Hx.
  assert (SEG : forall b n, In (b, n) (map uns2 (segments_reserved asegs)) -> In (b, b + n) (resv_of V)).
  { intros b n Hin. apply in_map_iff in Hin. destruct Hin as ([a m] & E & Hin). unfold uns2 in E. cbn [fst snd] in E. injection E as <- <-.
    unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. right. apply in_map_iff. exists (a, m). split; [reflexivity| exact Hin]. }
  rewrite reserved_eval in SEG.
  destruct (Z_lt_le_dec x 196608); [| destruct (Z_lt_le_dec x 716800); [| destruct (Z_lt_le_dec x 724992)]].
  - exists (65536, 65536 + 131072). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
  - exists (196608, 196608 + 520192). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
  - exists (716800, 716800 + 8192). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
  - exists (724992, 724992 + 5619712). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
Qed.

End CANSEC1.
Local Ltac inled := cbn; repeat (first [left; reflexivity | right]).
(* [comment removed for export] *)
Local Ltac pv PF k lo hi :=
  let H := fresh in pose proof (pfact_find _ (PVar k lo hi) PF ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok] in H.

Section CANSEC2. Context {rc : runConstT}.
Theorem aresv_ok_handoff : forall V (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) asan_pure_facts ->
  aresv_ok (mkALayout (LV V) w U) (resv_of V).
Proof.
  intros V w U PF.
  pv PF 78%nat 1549 34359736304. pv PF 207%nat 1549 34359735410. pv PF 208%nat 4295491576 34326181871.
  pv PF 226%nat 1549 34359734272. pv PF 227%nat 1 34359736319. pv PF 228%nat 1549 34359736304.
  pv PF 245%nat 1 34359736319. pv PF 310%nat 1 34359736319. pv PF 377%nat 1549 34359733495.
  pv PF 453%nat 1549 34359736064. pv PF 454%nat 1549 34359734272. pv PF 471%nat 1 34359736319.
  unfold aresv_ok, al_space_beg, al_ptr_array, al_t, al_ctx, al_nodes, al_store, al_fake. cbv [al_V LV Nat.eqb].
  split; [apply resv_img|].
  split.
  {
    intros x Hx.
    destruct (Z_lt_le_dec x 0x8fff7000); [| destruct (Z_lt_le_dec x 0x2008fff7000)].
    - eapply (resv_lit V 2147446784 268435456 KRWLAZY); [inled| lia| lia| | | exact (conj (proj1 Hx) l)]; cbn; lia.
    - eapply (resv_lit V 2415882240 2199023255552 KNONELAZY); [inled| lia| lia| | | exact (conj l l0)]; cbn; lia.
    - eapply (resv_lit V 2201439137792 15392894357504 KRWLAZY); [inled| lia| lia| | | exact (conj l0 (proj2 Hx))]; cbn; lia. }
  split; [eapply (resv_named V 208 137439023104 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 226 8388608 KNONELAZY); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 227 4096 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 228 65536 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 453 1048576 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 454 8388608 KRWLAZY); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 377 11571200 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 310 4096 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 78 65536 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 207 3727360 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 245 4096 KRW); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 471 4096 KRW); [inled| lia| lia| lia| cbn; lia]|].
  eapply (resv_named V 471 4096 KRW); [inled| lia| lia| lia| cbn; lia].
Qed.
End CANSEC2.
