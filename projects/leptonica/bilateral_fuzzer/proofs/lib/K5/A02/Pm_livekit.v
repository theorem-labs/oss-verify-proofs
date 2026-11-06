(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Pm_livekit () := "C69OSSVerify5KrLib2K53A028RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53A028RT_iface3ARTC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53A028RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C46Stdlib5Lists4List8in_splitI47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List9in_app_orI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or02C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib2K53A028RT_iface<af_live_disjC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c69OSSVerify5KrLib2K53A02:Pm_livekit>live_base_sizeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section LiveKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma live_base_size : forall Σ (m : mem) p n1 n2, ART RT Σ m -> In (p, n1) (rt_live RT Σ) -> In (p, n2) (rt_live RT Σ) ->
  0 < n1 -> 0 < n2 -> n1 = n2.
Proof using AF.
ltac2:(KReplay.run1 (kr_t_Pm_livekit ()) ["LiveKit"] "p'0h02l2h11Xh21Hh33Hi2h42l1h51Eh64__p1h74__x1h84__x2h94__x3h:1ei001eh;1Dh<2HAh=3Heqh>3Hi1h?3Hi3h@2NEhA2P1hB2P2hC7__arithhD4__ffhE8__varmaphF5__withG1lhH1mhI2n1hJ2n2hK1pi011phL1si021shM2Σi031ni041xi051zp;1p;3p;2p;4p;6p;5p;=p;7p;8g0000j1gTg000hj17Tg001Mj1ETg001kj1CTg002Nj1fTg0030j3ZTg003hR0j2VTg004Hj24Tg005Dj30Tg005[j2BTg0067j2JTg006Wj1@Tg0070R1j2dTg007Pj4]Tg007mj1GTg008Mj36Tg008jj33Tg009DR2j2<Tg009^j6UTg00::j5TTg00:XR3j28Tg00;2j3STg00;Lj6RTg00;ij2DTg00<Hj3QTg00<bj5MTg00=@l=LTg00>Aj2;Tg00>^j29Tg00?:j1KTg00?Zj2ATg00@8j4NTg00@Vj1OTg00A4j1PTg00A_j1ITg00BDj2?Tg00Bgj3FTg00CJj4:Tg00D5j7eTg00DYj1cTg00E;j2bTg00E^j6`Tg00FBj2\Tg00Fdj2[Tg00G>j2YTg00Gjj3^Tg00HIj4_Tg00I;j4HTg00I[j3XTg00J;j7aTg00J_j8WTg00KCR4P4f1R5f0R6CHp=1A3456p=5f3R7P4P4f2R8P5CH;X6p=2P5g00KaR9g00L@R:P:g00L`R;P6g00M@Fap==P7P9P:P:P;P8P5P6GWp=>p,2RTR<#gg00M`R=#7R>#7#7R?#7#7#7#E#C%E?#C#f[f4R?=Z<71V44R@1178f5RA,4<3011?8f6RB,4<50@g00NERC/B?RD1JBA15BARE%@E'dP1f7R1/5BRE%@Ef8RE/51RFP6P6X5FP6O1%@Ff9RF/5EP@f:RG/1Ff<RH,4<PBC]%G@RIf>RJ,4<P@PHf;RKP6C296@553IX0I,<IX4I'<P2PIf?RL,4<P@f=PHP6C296@553IX0I,<IX4Ig00NcRHP6fARM,4<P@PLPJP6C296@553IX0I,<IP2PIfBR2,4<P@f@RNPLP6C296@853IX0IPHP6fDRO,4<P@P2PMP6C296@?53IPIfERP,4<11O2RQ=0@6XGIPJP@fCRRP2P5C296@ARSP6EU11RMRT=0@SP@PBP@POPRP8C2RSPQP6DTA0@QBA0@QS'8P@P1P711PRRSP3A0@S1P@PPPOP7C290@SfFRS/1ORQ=0@EREA0@Q?'8P6fGRU/1PRV=0@FA0@VARF;S6X1EP6O1P@PSPPP?C290@QP311US=3@VPFfHRF/1SRV=0@GA0@VBR3'8P611FU=3@VP@P4P0P4P4P4P6P6n2001101000120105105X:@fIR0/1F110URVP6ER15FU150FP6fJRF/50fL/1FRF=0@JA0@FG'8P2P6O1'Db=W1P6O1b2W1P6O1A0@VKA0@V1;Q6X13P6O1n200100000021000010000W2P6O1n200100000021000010000DMb3b3A6@A590@TP<p,2AFPSPPPOPRPOP2PBP8PMP5P6M=L1;OR/9O1;O2/9O'8p-0R2g00O@RR#K%GRP41A48P51A47CN%O4%P4R7P7P9P:P:P;P4%I=,?4RR1?4=R=5F4g00OlRMPRC:,=7P41?4>R>9F4RPMPRC:,=7Fe%c:RRP7P41b4CRMg00PSR<P>C:,=7PRP7P4PMP<P=C:,=7PRP7P9P:P:P;PAE`C>C>C>1\7;P6P8g00Q:R7g00QZR;'[1Y68=37;dA^4C5C_bDbEbFX74X84X94W61;86/981;85/98'81BC8RCPB\C[[^74^84^94^62P6PHPSPOPPP5PLPNO7bCb;b?W5X0IP5P6O2n2001000000121104000W2X4IP5P6O2n2001000000121104000b:'DW@P6O1n200110200021010011103bLXBDWAW3W>W<XJ4XI4XK4WHWMo"). Qed.

(* [comment removed for export] *)
Lemma live_size_ne : forall Σ (m : mem) p n q k, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> In (q, k) (rt_live RT Σ) ->
  0 < n -> 0 < k -> n <> k -> p <> q.
Proof using AF.
ltac2:(KReplay.run1 (kr_t_Pm_livekit ()) ["LiveKit"] "h02H2h11qh21Eh32H1h42HAh52NEh62P1h72P2h81kh91mh:1nh;1ph<2Σp;1p;3p;2p;:p;7p;4g0000j1?Tg000hj10Tg001Mj15Tg001kj14Tg002Nj1>Tg0030j3:Tg003hj29Tg004Hj22Tg005Dj33Tg005[j27Tg008jj36Tg006Wj18Tg00R:l:=Tg009^j7<Tg00I;j4;Tg00KCR0P0f1f0R1C;p=1p,2RTR2#?g00M`#0#0#0R3#0#0#0#5#4%53#4#>[f5R3f4R45:21900R5f3R6,14f6R7,2233f2R8,16f7R9,22535g00NER:/7317:4A6093#8f9=609R3P0f:R:f8R;,11f=R<,22535g00Nc]0X1011:9f<R=,22535P8P<P=f;P:P;P9P7P1P4P6M:=O1W0P;P1P4F<W2%83eW5W7W6W0W3W4X80X10X:0X;0W9W<o"). Qed.

(* [comment removed for export] *)
Lemma live_head_apart : forall Σ (m : mem) p n rest q k, ART RT Σ m -> rt_live RT Σ = (p, n) :: rest -> In (q, k) rest ->
  p + n <= q \/ q + k <= p.
Proof using AF.
ltac2:(KReplay.run1 (kr_t_Pm_livekit ()) ["LiveKit"] "h01Eh11Hh22HAh31kh41mh51nh61ph71qh84resth92Σp;1p;2p;3p;4p;=g0000j1>Tg000hj10Tg001Mj11Tg001kj13Tg002Nj1=Tg003hj2:Tg007mj17Tg0030j35Tg004Hj26Tg00I;j42Tg00I[j34Tg008jj38Tg005Dj39Tg00?:j1<Tg00=@l=;Tp,2RTR0#>g00M`#0#0#0R1#0#0#0#1#3%11#3#=[g00KCR11:11R2#7R3f6R4f5R5550f7R6,60P1P1P5f4R7C2f3R8542583P1P1P8f2R3C2=927P0p,2AFf9f8P6P4P7P8%<2P5P3f1f0M=;W1W0W2X31X71W8X51W6W4W9o"). Qed.
Lemma live_second_apart : forall Σ (m : mem) p0 n0 p n rest q k, ART RT Σ m -> rt_live RT Σ = (p0, n0) :: (p, n) :: rest -> In (q, k) rest ->
  p + n <= q \/ q + k <= p.
Proof using AF.
ltac2:(KReplay.run1 (kr_t_Pm_livekit ()) ["LiveKit"] "h01Eh11Hh22HAh31kh41mh51nh62n0h71ph82p0h91qh:4resth;2Σp;1p;2p;3p;=p;4g0000j1ATg000hj10Tg001Mj14Tg001kj13Tg002Nj1@Tg003hj2:Tg007mj19Tg0030j38Tg004Hj27Tg00I[j32Tg008jj35Tg005Dj36Tg00?:j1?Tg008Mj3>Tg00<Hj3;Tg00=@l=<Tg00I;j4=Tg00KCR0P0f1R1f0R2C=p=1p,2RTR3#Ag00M`#0#0#0R4#0#0#0#4#3%44#3#@[1:00R4#9R5f8R6f7R7583f9R8,73f6R9,17f5R:f4R;'1f3R<524524555f2R5,1<=64;P3p,2AFf;f:P7P9P;P<1186R8%?4R6524P:P5P111;<R<9548A>46:964<;;2M=<W1W0W2X30X90W:X50X70X60X80W4W;o"). Qed.
End LiveKit.
