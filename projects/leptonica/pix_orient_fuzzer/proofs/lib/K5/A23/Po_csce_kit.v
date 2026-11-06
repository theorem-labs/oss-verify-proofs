(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Pm_iface Pm_iface2 Pm_iface4 PmF_kit Cf_iface RT_fk D_iface D_defs Bi_fktw Bi_fkweak Bi_iface2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Po_rows Po_iface Po_udd_kit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_csce_kit () := "C46Stdlib5Lists4List9app_assocC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53A238Po_iface4s_sxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib2K53A238Po_iface6s_rowpC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List3revC69OSSVerify5KrLib2K53A238Po_iface6s_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface4s_syC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib2K53A238Po_iface<sel_new_liveC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib2K53A238Po_iface4selv00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53A237PmF_kit@pm_copy_live_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface=pix_copy_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237PmF_kit;pm_copy_newC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A23:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A23:Lept_iface5cmapv00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:length_mapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:length_revC46Stdlib5Lists4List:length_appC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula04I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K53A237PmF_kit?pm_copy_new_lenC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sel_new_live_app0 : forall sel sv (L : list (Z * Z)), sel_new_live sel sv L = sel_new_live sel sv [] ++ L.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csce_kit ()) [] "h02rph11Lh21lh33selh42svp;2p;1p;4p;3p;6g0000R0p4p710g000NR1p4p710p8g000jj2DTg001Jj1CTg001jj12Tg002Oj15Tg002mj1=Tg003fj23Tg004Cj1:Tg005>j49Tg005Zj27Tg0062j16Tg006mj18Tg007fj1>Tg008Fj34Tg008fj30Tg009Cj3<Tg009]j2BTP0j4ATP1j6@Tg00:7j3;Tg00;8j4?Tg00;XR1P1f1R0f0R2C?p=1g00<61D11R3#CR4P4P1P3g00=1#2#2R5#5R6f2R7#='3,12X01%:0C9,73R8%60%25R5#5R9%80'3'1%25#2#5R5,17%>3R:543543R;=032503R<P1P3f3R=#=,36,12X01%:7C9,73%67%87,39'111=5=430543503=<42X241B4<A038;=032P3P8P;P2CAE@A;702A;70:=0325<4eW1W4X31o"). Qed.

Lemma pix_copy_live_app0 : forall p v cv (L : list (Z * Z)), pix_copy_live p v cv L = pm_copy_new p v cv ++ L.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csce_kit ()) [] "h01Lh12cvh21ph31vp;2p;1p;4p;3g000jj26Tg001Jj15Tg00=Vj40Tg00>Zj41Tg00?\j34Tg008fj32Tg009Cj33Tg00;XR0g00@[g00AX1600R0#5R1f3R2f2R3f1R4f0R5C0P2P3P4P5C1A4234=205531eW0W1W3W2o"). Qed.

Lemma length_sel_new_live0 : forall sel sv, Z.of_nat (length (s_rowp sv)) = s_sy sv ->
  Z.of_nat (length (sel_new_live sel sv [])) = s_sy sv + 2.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csce_kit ()) [] "h01xh14__x1h24__x2h31nh41Hh57__arithh64__ffh78__varmaph85__with94cstrh:2rph;3selh<2svh=1yp;1p;2p;4p;3p;<p;8p;6p;Bp;7g004Cj1=Tg00BVj21Tg00C6R0j12Tg006mj18Tg000jj2bTg001jj15Tg002Oj1:Tg002mj1VTg003fj2<Tg005>j4HTg005Zj2GTg0062j1DTg007fj1CTg008Fj33Tg00CVj29Tg00CmR1j24Tg00DJj1ATg009Cj1\j3BTg00Dij1ZTg009]j27Tg00EGl<WTg00Elj1UTg00FQj2TTg00Fmj1STg00GKj2LTg00Glj2>Tg00HUj3KTg00I>j3JTg00Igj2ITg001Jj1MTg00JSj2NTg00K1j1OTg00KOj4PTg00Kmj1QTg00LKj1RTg00M6j2?Tg00MYj4FTg00NDj1mTg00Nfj2lTg00OIj3@Tg00Olj8kTg00PPj2jTg00Q2j2iTg00Q^j3aTg00R=j4`Tg00Roj4_Tg00SZj4^Tg00T9j6;Tg00TWj2cTg008fj3]Tg00U6j3dTg00:7j3eTg00;8j4[Tg00UUlBfTg00V;l<gTg00V`j7hTg00;XR2f1R3f0R43Bp=0P2P2P3P4C[p=6g00WDR5P5P5P2P2P2g00WcP0P0P0P1g00XCf5R1f4R6f3R7f2R8P3P4MBfp=YP5P2P2P2P0P0P1P6P7P8P3P4M<gp=XP3g00XfR6g00YER1P1g00YeR0P4g00ZEFhp=Eg00<6%=4,12#2%84'0P51b22R9P2P9g00=1R:#5R;#5R<#:%V8'<,64X:2R=%=3R>CHR?,G9R@'1RA%D3%5<R<#:RB%83RC'<'6%5<#5#:R<,68%C9RD539539RE,19RF'9%24RG%88RH%:;RI'4RJ'0X35P5119?RK%D81<BH'6167<=39D539,19,94#2/0JX35RJP5112>R<PJg00ZeRJ#ARH#ARB,9<RL#2RM14CIRC'0%2<RN/4IRO/0CP2P2%\2RPP4X02RQPP1034#ZX=2X02PMPOPQPQ172GX05PLPOP<PN172NPBPI172IEYEXPCPC172CM<W%U<g00[DRB/TNg00[bRN%S:,L21>2H5K21>2J5J2g00\N'I%CN33%MNP21N28P3%O2CP%Q2%R2RNP6P1P1P0P21?2:R:g00]:R61?2;R;CF,EN%m1P21l2IR19@2:P6A@2;1CF,ENGk1jN0P4P8g00]aRNg00^AR0'71i48=BN0dAa2B3C`b6b7b8X12X221043143I148I'0[^12^22P4%87%=7,12#2P8O3b5b9C_19<F#2/0CePKP2P9P=P>C^E;PA1c9?E;A]9@E,19Ad9@EE;Ae83D,19#2/0CeW4W<X;2o"). Qed.

Lemma length_pm_copy_new_le : forall p v cv, (length (pm_copy_new p v cv) <= 4)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csce_kit ()) [] "h02cvh11ph21vp;3g00^aj30Tg00;Xg00@[g00AXf2f1f030W0W2W1o"). Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Po_csc_defs.
Definition CSCE_STOPS : list Z := [e_pixDestroy; e_pixRemoveBorder; e_pixCopy_po; e_selDestroy; csc_fl].
