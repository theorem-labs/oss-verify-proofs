(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_state RT_rep RT_facts RT_artfacts RT_icfacts I_consts I_qck R_m2s I_memcpyw I_memsetw I_memchrw I_strnlenw I_strlen R_isPoisoned I_lift I_lift2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_iclifts () := "C69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53A238RT_iface3ARTC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib2K53A238RT_iface9rng_classC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K53A238RT_iface7fs_sizeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K53A23:RT_icfacts<rta_shw_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:RT_icfacts=rta_shw_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:RT_icfacts=rta_shw_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:RT_icfacts;rta_shw_imgC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53A238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53A238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235I_qck8qc_wordsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238I_consts=region_in_memC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53A236RT_rep3RTAC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2K53A238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53A238RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K53A23:RT_icfacts>rta_icells_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:RT_icfacts=rta_icells_slC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236I_lift;memcpy_liftC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;RT_artfacts=rta_art_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_isPoisoned9rip_proofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23:RT_iclifts6rta_icC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23:RT_iclifts7rta_shwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236I_lift;memset_liftC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236I_lift;memchr_liftC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236I_lift<strnlen_liftC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237I_lift2;strlen_liftC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23:RT_iclifts6rta_slC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237I_lift2@asan_memset_liftC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237I_lift2@asan_memcpy_liftC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rta_shw : forall Σ m p n, ART RTA Σ m -> 0 < n -> rng_class RTA Σ p n -> qc_words m p n /\ region_in_mem p n.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iclifts ()) [] "p'0h01kh11Hh21fh32H1h42H2h51ph67__arithh73Hinh84__x1h92HAh:2HCh;2Hnh<4__ffh=8__varmaph>5__with?2k0h@1mhA1nhB2p0hC2Σi001xp;1p;3p;2p;4p;8p;;p;7g0000j1qTg000hj1GTg001Mj1KTg001kj1XTg002Nj1hTg0030j3bTg003hj2OTg004Dj4_Tg005Bj2LTg005bj21Tg006>j20Tg006[j1BTg007Wj1ATg0085j26Tg008RR0j2=Tg008lj1^Tg009Lj1]Tg009lj2\Tg00:Jj1[Tg00:hj1ZTg00;Sj2ITg00<6j2YTg00<Yj4WTg00=Dj1pTg00=fj8oTg00>Jj2nTg00>lj2mTg00?Fj2kTg00@2j3jTg00@Lj3iTg00@kj4gTg00A]l;fTg00B`l;eTg00Cdj8dTg00Dhj8cTg00Ejj4QTg00FJj2STg00GFj3CTg00G]R1j2:Tg00H8R2j2PTg00HRj2NTg00IPj2UTg00JKj3aTg00KEj2`Tg00LGj7lTf0R3#G#Gp=;g00LkR4P4f1R5P3CQp=Dg00MIR6/S3p=<f5R7f4R8f3R93Cf2R:1153':':p=H1P43p=4P4g00N?R;P5P3CQp=E1153,::p=F1N659C9:/:3p=91P;3p=?1U63p=>g00N^R<,65/03p=@119:1153':p=7g00O\,13p=811:5/:3p=2Aa89:1`53':p=510:5/13p=3AC9:5/:3p=J1S639C:5p=MP5g00PYR=g00Q8R>P>g00QXR?P3g00R8Flp=V1N639C:5p=T1U63/6<p=R%q6g00RXR<#G#;R@#GRA#;RB#K#X%K@#X#h[Ab69:g00S=RC/O5P6P7P9P:C_P01L44R61D53RDf8RE#<f6RF,15RG10F7RH1053RIEHX04#4X54#41L4;RJ1E53RKPE%B3RL,05%A@R@'6RM9FGHC9X0;#?X24#4%>F%ABRG'@P81089RNg00S[%AA'6RAC7%;B#;#;#;#;#ARB%8N728'='=PFP7P8P7P8D5P3P6PDf9RN#<f7RO,15RP10OFRQPIEHX04#4X54#4P2P4P6PDf:RR#<115ERS10EORTPIEHX04#4X54PEPOPFPOPFD5RUP3P6PDf<RD#<115RRV10RNRWPIEHX04#4P2P4P61D:3f=RI#<f;RX10:393XR52:CJX04PDPXPRPXPRD5RYP3P61D83f?RZ#<P8PI10IDR[1083C7CJP11D75f@R\5M6f>R]107593]I527P\PZP]PZP]D5P31DO9fBR^5M6fAR610E8936\52EP111N^10N793^6fDR_fCR`P^P`P^D5P311X_fERa10DE73_fHRbfGRcP_PIPNfFRdPaP7P5P3g00TZRe#^%]e1\45%[4%Z4ReP=P>P>P?P41I4Cg00UF1Y4<R=CW,Ve%p>P4%A<R<,I4g00UmP=CW,VeGo1ne?P3P:g00VTReg00W4R?'m1k3:=je?dAi4C5Cgb<b=b>X84R?1OC311<5[^84R<P3PdP_O2b6M;fW4W3P5P3O2n2001000000120000000W1W7P5P3O2n2001000000120000000W1X?4P5P3O2n2001000000121100000W1XB4P5P3O2n2001000000121100000W1P3O1PJPKPNAFPQMC9X0;#?X24#4%>O/@GP71078RPPAC7%8P92B7'='=P0PJPKPRAFSTMC9X0;#?X24#4%>E/@GPFPHPAC7%8H92BF'=PUP3PJPKPXP5PN10NERUPMC7C9X0;#?X24#4P2P4PJPKPDAFVWMC9X0;#?X24PRPNPEPNPED5RVP3PJPKP]A3DXM925DC9X0;#?P2P;PJ1E:3PZP:PIP[10:L/6@C7C9X0;P]PIPDPIPDD5P3PJ1E83P6108L/6@93Z]928ZC9P11E75=TJ^%B5,07/6@93\Z927\P^P6P\P6P\D5P31EO9=TJ_%B8,0E/6@93`^92E`P111N_%B7,0N/6@93_`PdPaP_PaP_D5P311Xd%BE,0D/6@93cdfJfIPdPIPNPbPcP7P5P3P?P<P3PbPdO2b6M;eW4W3P5P3O2n2001000000120000000W1W7P5P3O2n2001000000120000000W1X0;P5P3O2n2001000000121100000W1X24P5P3O2n2001000000121100000W1P3O1%>N/@GPOPQPAC7%8Q92BO'=P0%>R/@GPEPTPAC7%8T92BEPVP3%>X/@GPNPUPAC7P1%RD?3GR11WAPYP3%R]?3GD11[AP\PZPDP]PIP5P3P?P<P3P]PDO2b6R<GdW4W3P5P3O2n2001000000120000000W1P3O1%8U92BNP111BR%8WPYP311BD%8[P\PZPDP]PIP5P3P<GcW4W3P5P3O2n2001000000120000000W1P3O1n200100000021000010000W1P3O1n200100000021100011000W1P3O1n200100000021100011000P7P8P9P8P9D5R9eP9eW:W;W9XA4X54W@WCo"). Qed.

Lemma rta_ic : forall Σ m, ART RTA Σ m -> icells m /\ icells_ms m /\ icells_mc m /\ icells_sn m /\ m2s_cells m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iclifts ()) [] "h02HAh11mh22Σp;1p;3g0000j16Tg000hj10Tg001Mj12Tg001kj11Tg002Nj15Tg0030j34Tg00WTj33Tg00MIR0#6g00RX#0#0#0R1#0#0#0#2#1%21#1#5[f1R1f0R2540f2?312W0W1W2o"). Qed.
Lemma rta_sl : forall Σ m, ART RTA Σ m -> icells_sl m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iclifts ()) [] "h02HAh11mh22Σp;1p;3g0000j16Tg000hj10Tg001Mj12Tg001kj11Tg002Nj15Tg0030j34Tg00XYj33Tg00MIR0#6g00RX#0#0#0R1#0#0#0#2#1%21#1#5[f1R1f0R2540f2?312W0W1W2o"). Qed.

Theorem rta_memcpy : memcpy_icontract RTA e_memcpy.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iclifts ()) [] "p;5g00Y]j50Tg00MIg00Z[g00[`g00\bg00]_D0o"). Qed.
Theorem rta_memset : memset_icontract RTA e_memset.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iclifts ()) [] "p;5g00^]j50Tg00MIg00Z[g00[`g00\bg00]_D0o"). Qed.
Theorem rta_memchr : memchr_icontract RTA.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iclifts ()) [] "p;5g00_[j50Tg00MIg00Z[g00[`g00\bg00]_D0o"). Qed.
Theorem rta_strnlen : strnlen_icontract RTA.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iclifts ()) [] "p;5g00`Yj50Tg00MIg00Z[g00[`g00\bg00]_D0o"). Qed.
Theorem rta_strlen : strlen_icontract RTA.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iclifts ()) [] "p;6g00aXj60Tg00MIg00Z[g00[`g00\bg00]_g00bWE0o"). Qed.
Theorem rta_asan_memset : memset_icontract RTA e_asan_memset.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iclifts ()) [] "p;5g00cTj50Tg00MIg00Z[g00[`g00\bg00]_D0o"). Qed.
Theorem rta_asan_memcpy : memcpy_icontract RTA e_asan_memcpy.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iclifts ()) [] "p;5g00dXj50Tg00MIg00Z[g00[`g00\bg00]_D0o"). Qed.
