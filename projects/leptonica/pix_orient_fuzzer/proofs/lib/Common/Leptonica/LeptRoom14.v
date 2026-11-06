(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptRoom14 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c69OSSVerify5KrLib6Common9Leptonica:LeptRoom148RB_pix14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8LeptRoom6RB_pixC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9Leptonica:LeptRoom14<RB_pixcopy14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica:LeptRoomPC:RB_pixcopyC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib6Common9Leptonica:LeptRoom14<RB_graymorphC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8LeptRoom6roomtrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C69OSSVerify5KrLib6Common9Leptonica8LeptRoom=roomtr_weakenC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C69OSSVerify5KrLib6Common9Leptonica8LeptRoom6RK_pixC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9Leptonica:LeptRoom14;RB_pix14_leC1?~~~~~~~~~~~~~~~".
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RB_pix14 : Z := 2 ^ 26 + 2 ^ 23 + 2 ^ 22.
(* [comment removed for export] *)
Definition RB_pixcopy14 : Z := RB_pix14 + RB_cmapcopy.

(* [comment removed for export] *)
Definition RK_gm3 : Z := 3 * RK_pixcopy.      Definition RB_gm3 : Z := 3 * RB_pixcopy14.
Definition RK_gm4 : Z := 4 * RK_pixcopy.      Definition RB_gm4 : Z := 4 * RB_pixcopy14.
Definition RK_graymorph : Z := RK_deser + 4 * RK_pixcopy + 2 * RK_gm3 + 2 * RK_gm4.
Definition RB_graymorph : Z := RB_deser + 4 * RB_pixcopy14 + 2 * RB_gm3 + 2 * RB_gm4.

Ltac room_consts ::=
  unfold RK_graymorph, RB_graymorph, RK_gm3, RB_gm3, RK_gm4, RB_gm4, RB_pixcopy14, RB_pix14,
         RK_paintcmap, RB_paintcmap, RK_pixcopy, RB_pixcopy, RK_cmapcopy, RB_cmapcopy, RK_box, RB_box,
         RK_hdr, RB_hdr, RK_cmap, RB_cmap, RK_pix, RB_pix, RK_deser, RB_deser in *.

Lemma RB_pix14_le : RB_pix14 <= RB_pix.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptRoom14 ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h56__sat2h66__sat3h76__sat4h86__sat5h96__sat6h:6__sat7h;8__varmaph<5__witp;1p;2p;3p;4p;7g0000j17Tg000Uj13Tg0013j11Tg001Xj24Tg002@j22Tg002\j26Tg0039j35Tg003]j1ATg004=j1@Tg004]j1?Tg005;j1>Tg005Yj1=Tg006Dj2JTg006gj19Tg007Ej38Tg007hj3<Tg008Kj4ITg0096j7HTg009Zj2GTg00:<j2FTg00:Vj2ETg00;Bj3CTg00;\j3BTg00<;j4DTg00<mj2;Tg00=Jj2:Tg00=fR0f0R1':p=0g00>DR2#7R3#3R4%13#1R3#1R5#3R6'41204R7%061646R8,20[[%04R9g00>iR:f1R;9546UW0%08\:^09%73R3#3R6,44%061646R<,20[\7A546;V:X09%0<\:^09%12#7#1R2#1R6#3R=,44%0=164=R>,20[\7A54=;V:X09%0>\:^09%72R2#3R=,44%0=164=R?,20[\7A54=;V:X09%0?\:^09g00?ER9#A%@9g00@1R9#?%>9%=9R:g00@Og00@nR=P=g00ANR=P91J94R4%92589%9598945<9%9398945<9g00An%969894CIg00BUFH1G:=P1f2R=g00C5R:g00CUR4'F1E1==C:4dAB90;CDb2b;b<1;?8/;</:>P1b1b3b4b5b6b7b8b9b:g00D5g00E>':eo"). Qed.
Lemma RB_pixcopy14_le : RB_pixcopy14 <= RB_pixcopy.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptRoom14 ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h56__sat2h66__sat3h76__sat4h86__sat5h96__sat6h:6__sat7h;6__sat8h<6__sat9h=8__varmaph>5__witp;1p;2p;3p;4p;7g0000j13Tg000Uj12Tg0013j11Tg001Xj25Tg002\j26Tg0039j37Tg003]j1ATg004=j1@Tg004]j1?Tg005;j1>Tg005Yj1=Tg006Dj2KTg006gj19Tg007Ej38Tg007hj3;Tg008Kj4JTg0096j7ITg009Zj2GTg00:<j2FTg00:Vj2ETg00;Bj3CTg00;\j3BTg00<;j4DTg00<mj2:Tg00=Jj2<Tg002@j2HTg00=fR0f0R1'Hp=41<01p=0g00>DR2#3R3#2R4%13#1R5#1R6#2R7'5%44R8%071647R9#4[[%04R:g00>iR;f1R<9747UW0%09\;^0:%35R5#2R7,54%071647R=#4[\8A747<V;X0:%0=\;^0:%33#1#3R3#2R7,54%071647R>#4[\8A747<V;X0:%0>\;^0:%12#3#1R2#1R7#2R?,54%0?164?R@#4[\8A74?<V;X0:%0@\;^0:%32R2#2R?,54%0?164?RA#4[\8A74?<V;X0:%0A\;^0:g00?ER:#A%@:g00@1R:#?%>:%=:R;g00@Og00@nR?P?g00ANR?P:1K:4R4%9258:%9698:45;:%9598:45;:%9398:4R35;:g00An%9798:4=;:3CJg00BUFI1G;?P1f2R?g00C5R;g00CUR3'F1E1?=C;3dAB:0<CDb2b=b>1:A9/:=/:>1:@>'<P1b1b3b4b5b6b7b8b9b:b;b<g00FCg00GP'<eo"). Qed.
Lemma RK_graymorph_val : RK_graymorph = 77.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptRoom14 ()) [] "p;1p;2g0000j10Tg0013j11Tg000Uj13Tg00:<j22Tg00@1g00>D#0#0#1#1#0#1#3'2o"). Qed.
Lemma RB_graymorph_le : RB_graymorph <= 2 ^ 31 - 2 ^ 26.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptRoom14 ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h57__sat10h67__sat11h76__sat2h86__sat3h96__sat4h:6__sat5h;6__sat6h<6__sat7h=6__sat8h>6__sat9h?8__varmaph@5__witp;1p;2p;3p;4p;7g0000j13Tg000Uj11Tg0013j12Tg001Xj27Tg002\j25Tg0039j38Tg003]j1ETg004=j1DTg004]j1CTg005;j1ATg005Yj1@Tg006Dj2?Tg006gj1;Tg00H[j3<Tg00I>j3QTg008Kj4PTg0096j7OTg009Zj2NTg00:<j2JTg00:Vj2ITg00;Bj3HTg00;\j3FTg00<;j4GTg00<mj26Tg00Iaj2=Tg00J>j2KTg00=Jj2>Tg002@j2BTg007Ej3LTg007hj3MTg00=fR0f0R1'Bp=41>01p=0g00@1R2f1R3;L1p=:AM231p=9g00>DR4#3R5#1R6%25#2R7#2R8#1R9'7%46R:%091569R;#4[[%06R<g00>iR=A8693UW0%0;\=^0<%24R4#2R9#3#3R>#1R?,76%0?156?R@#4[\:A86?3V=X0<%0@\=^0<%37R7#1R?,76%0?156?RA#4[\:A86?3V=X0<%0A\=^0<%29#2R9#1R?,76%0?156?RB#4[\:A86?3V=X0<%0B\=^0<%35R5#2#3R?#1RC,76%0C156CRD#4[\:A86C3V=X0<%0D\=^0<%34#2#3RC#1RE,76%0E156ERF#4[\:A86E3V=X0<%0F\=^0<g00?ER<#E%D<%C2%A2%@2R<g00@Og00@nR=P=g00ANR=P21?26RE%;>':%15R5,?2%;C,:ERC%;8,:E'9%;7,:E'9%;?,:E'9R?5<2R7'9%14R4,?2=<2?9<2E'9A<2E7'9g00An%;9,:E=Q2CCPg00BUFO1N<=P1f2R=g00C5R<g00CURC'J1I1==H<CdAF203CGb2b?b@16F;/6A/6DRD,=5R5,6@1=4D,=6'61=65'61KBFRF'>P1b1b3b4b7b8b9b:b;b<b=b>b5b6g00J[/>Feo"). Qed.

(* [comment removed for export] *)
Section Weaken.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Lemma roomtr_pix14_pix : forall A vm A' vm', roomtr A vm A' vm' RK_pix RB_pix14 -> roomtr A vm A' vm' RK_pix RB_pix.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptRoom14 ()) ["Weaken"] "h04__x1h11Ah22A'h31Th47__arithh54__ffh68__varmaph75__with82vmh93vm'p;3p;2p;9p;1p;4p;7p;>g00Khj3CTg00M1j3BTg00N:j20Tg00O;l91Tg003]j1ATg004=j12Tg00P@j23Tg005;j14Tg005Yj15Tg00P^j26Tg008Kj47Tg0096j78Tg009Zj29Tg00:<j2@Tg00:Vj2:Tg00;Bj3;Tg00;\j3<Tg00<;j4=Tg00=Jj2>Tg00QAl>?Tp,2ALR0p,2CLR1p,3ASRR29C015B0'0R3g00RMR4P0P1P2f3R5f2R6f1R7f0R8g00SDR9g00D5R:M91P0P1P2f4P5P6P7P9P:P9g00E>P8g00@1R:g00?ER5#A%2513:7%4:%5:R5g00@Og00@nR2P2g00ANR2P:g00>D,6:R1g00AnP1C7g00BUF81952P8P6g00C5R2g00CUR5'@1:86=;25dg00=f=<:7C=b5b6b7W01>88^0:P8P9O1b4g00TIM>?W3X94X23W8W1o"). Qed.
End Weaken.
