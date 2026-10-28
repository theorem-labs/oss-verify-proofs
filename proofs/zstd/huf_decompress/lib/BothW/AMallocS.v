(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF SysStepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes ASecFacts AMalloc_iface ADepot_iface APoisonR_iface ARep ALayout AHeapP
     ARepKit ARepFrame ARepExt ARepExt2 AKit AKit2 AKitQ AModelFacts APrimFacts ASec ASecFrame ASecModel ASecStore
     F_apoison F_ammap F_aalloc1 F_amalloc_icpt F_amalloc_preS F_alarge F_acallocS F_amalloc_tailS F_amalloc_arep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AMallocS () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstI5ARocqVerifyHarness?AgentSubmission4Spec5STree5stree00C47Corelib4Init5Logic8eq_ind_rI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl2AMI5ARocqVerifyHarness?AgentSubmission3Lib5ITree5itree00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6aembedC35stdpp4gmap9gmap_foldC5ARocqVerifyHarness?AgentSubmission3Lib5ITree5ebindC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4base4fmapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp8fin_maps@lookup_insert_eqC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4sclrK46Stdlib9micromega6VarMap1t01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4iclrC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divK46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFK46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5BothW7ALayout4aobjC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission4LibA8SysStepF?implF_from_evtFC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5implFC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA6epostFC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA=implF_ret_unrK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00".
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6352896 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_AMallocS ()) ["CANSEC1"] "h01Hh14__p1h24__x1h34__x2h44__x3h51kh62H1h77__arithh84__ffh98__varmaph:5__with;2H0h<2hih=2lop;3p;1p;2p;4p;6p;7p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000nR1p4p710p1001ep4p710R0p8P1p4p7210P0p8p1002Cp4p710R1p1002aR2p4p710R3p8P1P2p4p7210R2p8p1003:p4p710P0p8p1003op4p710P0p8p1004ep4p70R4P0p8P4p1005\p4p7210p8P4p1006VR5p4p710p8P4p1006mp4p73110p8P4p1007aR6p4p710p8P4p1008=p4p710p8p1008VR4p4p73101R7p10090R8p4p73110p8P7p1009IR9p4p73110p8P7p1009ep4p710p8P7p100:8R:p4p7201p8P7p100:Jp4p7201p8P7p100:\R;p4p73110p8P7p100;0R<p4p73110p8P7p100;DR=p4p73110p8P7p100;^p4p7201p8P4p4p710R7P8p4p710p8P7P9p4p710p8P7P3p8P7P2p8P7P;p4p710p8P7P<p4p710p8P7P=p4p710p8p100<1R=p4p710R7P1p8P7P3p8P7P2p8P7p100<Ep4p73110p8P=p4p741110R=P6p4p73101p8p100<Wp4p7210P0p8p100=Cp4p7<111111111110P0p8p100=ep4p741110R0P4p4p7511100R6p8P6P0p8p100>>p4p741110R0P4p4p76111100R6p8P6P0p8p100>Vp4p741110R0P4p4p771111100R6p8P6P0p8P5p4p741110R5P4p4p7:1111111100R4p8P4P5p8P:p4p7200R:P=p8P=P:p8g00?6j3bTg00?kj1aTg00@ij15Tg00ANj11Tg00B3j1:Tg00BQj1OTg00CGj20Tg00CcR:j2<Tg00D>j2=Tg00D[j2DTg00E8j2ITg00ERj1CTg00F1j2BTg00FZj3HTg00GCj2VTg00Goj1UTg00HOj3TTg00Hoj1STg00IOj2ETg00Imj4RTg00JKj1QTg00Jij1PTg00KTj2ATg00L7j6NTg00L[j1MTg00M=j2GTg00M`j3@Tg00NCj3FTg00Nfj2LTg00OHj2`Tg00Obj2_Tg00PNj3^Tg00Phj3[Tg00QGj4ZTg00R9j4JTg00RSj4YTg00S>j7\Tg00Sbj7WTg00TFj8]Tf0R=#5#5#5#5p=7%5=#5p=X%1=#1p=?%1=#1#1#1p=9%1=#1#1#1#1#1#1#1p=3f2R5f1R4'0/<=p=21<4=,<5p=>g00TjR0/G=p=8P5g00UHR6g00UgR7P7g00VGR2P0P4g00VgP=CYg00WNF\p=4P5P6P7P7P2P4P=FWp=6f3R3P6P7P7P2P5P4P=G]p=;104=,<5p=Kp,2rcR1?b4=%a1g00WnR<#5R;#5#7#7#7R9#1#5#XR8#5#7#1#?#9#3#3#:R>%O1R1'0R?%59#7#7#1#?#9#3#3#:R9,01R@'<g00XS%5<#1#9#7#9#3#:RA/03RB%98#3#:R8,05RC'<%1<RD#9#3RE#7#7#7#7#1#?#9#3#:RF1051723g00XmRG%:<RH,0=72=RIf5RJ,0ARK1=F=RLf4RM%1E#?#3#3#3#3#3#3#:RE,==,D8RN10M1RO3272J3>X50,I0P4103892AMP:PK10M8f7RK,0ARPf6RQ10Q172N92LK5>IX50,I0RQP=10K8P0f:RR,0Af9RS10S172N92LR5>IX50RIPGp-0RLg00YKRNg00Z7RT#C#CRU#C,B01B0U1B0T5H05H0g00ZV'V%UN3TRT%SNRNP01E05P41E03CRRU%Q0RV%P0RW%8>1A0;R;54WPWP6P7P7P2PJENR656W%M7R7PW1A0DRD%88RX54WP7PW%8A1A0<R<54WRYP71G0GRZ=4WZ%8HR[94WZR\56W%8FR]=@0Z=4W<%8ER^9@0Z9F0X94WDA4WD;RZ56W56W96WY56WC;C;C;1LW2R2P=P5g00[BR_g00[bR`'`1_=5=^_`dA[0G4CZR`b8b9b:X20X30X40W1A2>5310A510GHRA92GG1=FG1=GE,D810MJRG52M7237>B[\C[^20^30^40^1LP=P@P1PSPRPKP4P5O7b7CJW6X0PP4P=O2n2001000010121000000W0P=O1103192FMP:10FJPOPQP=10FK10K1P0PIPHPTPNPUPVPW%8994W;96W6P7PWPZP7PWA4W]<P7A4W[[96W\A@0][=4W<A@0[^9F0X94WD=6WZ56W96WY56WC;C;C;P2P`b8b9b:X20X30X40X1LAK359105310F5AKAHH1=FH1=HE,D8=2MG7237>B[[[^20^30^40^1LP=P?P1PSPRPKP4P5O7b7CJW6W0P4P=O2n2001000010121000000W0P=O1n200100001021100011000b;W0X<0X=0o"). Qed.
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_AMallocS ()) ["CANSEC1"] "h04__x1h14__x2h21Hh37__arithh44__ffh58__varmaph65__with71kh82G1h92G2h:1ah;1np;2p;1p;4p;3p;7p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000nR1p4p710p1001ep4p710R0p8P1p4p7210P0p8p1002Cp4p710R1p1002aR2p4p710R3p8P1P2p4p7210R2p8p1003:p4p710P0p8p1003op4p710P0p8p1004ep4p70R4P0p8P4p1005\p4p7210p8P4p1006VR5p4p710p8P4p1006mp4p73110p8P4p1007aR6p4p710p8P4p1008=p4p710p8p1008VR4p4p73101R7p10090R8p4p73110p8P7p1009IR9p4p73110p8P7p1009ep4p710p8P7p100:8R:p4p7201p8P7p100:Jp4p7201p8P7p100:\R;p4p73110p8P7p100;0R<p4p73110p8P7p100;DR=p4p73110p8P7p100;^p4p7201p8P4p4p710R7P8p4p710p8P7P9p4p710p8P7P3p8P7P2p8P7P;p4p710p8P7P<p4p710p8P7P=p4p710p8p100<1R=p4p710R7P1p8P7P3p8P7P2p8P7p100<Ep4p73110p8P=p4p741110R=P6p4p73101p8p100<Wp4p7210P0p8p100=Cp4p7<111111111110P0p8p100=ep4p741110R0P4p4p7511100R6p8P6P0p8p100>>p4p741110R0P4p4p76111100R6p8P6P0p8p100>Vp4p741110R0P4p4p771111100R6p8P6P0p8P5p4p741110R5P4p4p7:1111111100R4p8P4P5p8P:p4p7200R:P=p8P=P:p8g00\Bj2WTg00CGj20Tg00D[j22Tg00ANj11Tg00B3j1;Tg00@ij16Tg00Ccj23Tg00D>j29Tg00E8j2VTg00Goj1UTg00Hoj1TTg00IOj2PTg00]7j1OTg00Imj4NTg00JKj1LTg00Jij1KTg00M=j2:Tg00KTj2ATg00L[j1ITg00NCj3>Tg00M`j3=Tg00Nfj2HTg00OHj2JTg00Obj2GTg00PNj3FTg00Phj3MTg00QGj4ETg00R9j4CTg00RSj4QTg00S>j7DTg00Sbj7RTg00TFj8STf0R:#1#1#1#1p=?%1:#1#1#1#1#1#1#1p=5%1:#1p=B%6:#6p=@%6:#6#6#6p=7f2R=g00UHR5g00UgR4P4g00VGR0g00TjR6f1R7g00VgP:CQg00WNFDp=4P=P5P4P4P0P7P:FRp=8f3R2P5P4P4P0P=P7P:GSp=<1W7:g00XmR5/0=122=g00WnR3#1R1#?#5R<#1#B#5#5#5#5#5#5#;R;'0g00XSf4R9/22%@3#7#7#7#1#6#@#?#5#;R8'0%7<#7#7#7#1#B#?#5#;R</09105:R>%;3R?,0:'3R@f6RAf5RB'219:;,28RC'019<:RD/0A'3'3X76,V6P=12B9/08P6f7RE/2A/0C10DE'3,3@X76R@P5g00YKRD#URC%TDRDP61P6=P7%O6CNRF%L6RG%K6RH1:65RI1A63R354H%I4R4PH1A619>63R11:68RJ54HP4A4HII1:6?RK94HIRL58H1:6;RM9=6I9>6J94H11:6<RN==6I=4H358H58HC<C<1HH0R0P:P=g00[BRIg00[bRO'J1G:==FIOdAM657CEROb4b5b6X06X16127=/081055105?RI'312=2RP195;,28'019<5/0='3'3[\>^06^16P:PAPEP9P7O4b3CCW2P:O110<BP6P@P?PCPDPFPGPHA4H1MP4PHA4HN3P4A4HKK98HLA=6KM9>6J94H1A=6NK=4H358H58HC<C<P0POb4b5b6X06X1612:7/0;10<710??,3I19?;,28,0P19<?/0='3'3[[^06^16P:PAPEP2P7O4b3CCW2P:O1n200100001021100011000W9W8W2X;6X:6o"). Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6352896 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_AMallocS ()) ["CANSEC1"] "h04__x1h14__x2h22H0h31kh41Hh57__arithh64__ffh78__varmaph85__with92G2h:1ah;1np;2p;1p;4p;3p;7p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000nR1p4p710p1001ep4p710R0p8P1p4p7210P0p8p1002Cp4p710R1p1002aR2p4p710R3p8P1P2p4p7210R2p8p1003:p4p710P0p8p1003op4p710P0p8p1004ep4p70R4P0p8P4p1005\p4p7210p8P4p1006VR5p4p710p8P4p1006mp4p73110p8P4p1007aR6p4p710p8P4p1008=p4p710p8p1008VR4p4p73101R7p10090R8p4p73110p8P7p1009IR9p4p73110p8P7p1009ep4p710p8P7p100:8R:p4p7201p8P7p100:Jp4p7201p8P7p100:\R;p4p73110p8P7p100;0R<p4p73110p8P7p100;DR=p4p73110p8P7p100;^p4p7201p8P4p4p710R7P8p4p710p8P7P9p4p710p8P7P3p8P7P2p8P7P;p4p710p8P7P<p4p710p8P7P=p4p710p8p100<1R=p4p710R7P1p8P7P3p8P7P2p8P7p100<Ep4p73110p8P=p4p741110R=P6p4p73101p8p100<Wp4p7210P0p8p100=Cp4p7<111111111110P0p8p100=ep4p741110R0P4p4p7511100R6p8P6P0p8p100>>p4p741110R0P4p4p76111100R6p8P6P0p8p100>Vp4p741110R0P4p4p771111100R6p8P6P0p8P5p4p741110R5P4p4p7:1111111100R4p8P4P5p8P:p4p7200R:P=p8P=P:p8g00]Uj2YTg00ANj11Tg00B3j1<Tg00CGj20Tg00@ij1:Tg00XSR:j2DTg00D[j23Tg00D>j27Tg00E8j2ETg00Goj1VTg00Hoj1UTg00IOj2TTg00]7j1RTg00Imj4QTg00JKj1PTg00Jij1NTg00KTj2BTg00NCj3@Tg00M=j28Tg00L[j1KTg00M`j3>Tg00Nfj2JTg00OHj2ITg00Obj2HTg00PNj3MTg00Phj3GTg00QGj4OTg00R9j4CTg00CcR=j2?Tg00RSj4FTg00S>j7STg00Sbj7XTg00TFj8WTf0R5#1#1p=L%15#1#1#1#1#1#1#1p=5%15#1#1#1p=Af2R4f1R0'3/05p=;1040/?5p=61?05,?4p==P4g00UHR6g00UgR7P7g00VGR2g00TjR3P0g00VgP5CFg00WNFSp=2P4P6P7P7P2P0P5FXp=4f3R1P6P7P7P2P4P0P5GWp=91Y05g00WnR6#1R<#1#L#5R;#AR9#5#5#5#5#5#5#<R89;40P=%<;R;/01R=%<9R99;14%:6#1#A#:#:#:#:#A#5#<R>/01'Dg00XmR?%<6R@,05765RAf5RB,0;RCf4RD,3B1758,39RE17>5RF/0B363=X33,E3P0f6RG?;B910>G'DP:f7R:?;G910>:f9RG,0;f8RB,3G10FG76E5=AX33,E3P5A;B:9P3f:RH,0;13HG10FH76E5=AX33RAP?g00YKRE#VRF%UEREP31T34P0%R3CQRI%P3RJ%N3RK1B36R61B3<5@3R<1839RL52K%K7R7PK183;=2K6RMP7183?RN=2KN183@RO92KNRP54K1838RQ9>3N9@3L92K<183>RR=>3N=2K654K94KM54KC9C91JK2R2P5P4g00[BRNg00[bRS'I1H54=MNSdAG3?0CORSb6b7b8X03X131350RN/0910;010?@RT96??10;4R;134117?8,3917>?/04363=[[^03^13P5PGPHP0PDO4b5CCW2P5O110>BP3PAP@PFPEPIPJPKA2K<QP7PKA2KR6P7PKPMP7A2KOO94KPA>3OQ9@3L92K<A>3RO=2K654K94KM54KC9C9C9P2PSb6b7b8X03X1310N810>010@@,?T131D17@8,3917>@/01367==\;[[^03^13P5PGPHP:P0PDO5b5CCW2P5O1n200100000021100011000W2X4CP0P5O2n2001000000121000000W9W4X;3X:3o"). Qed.
(* [comment removed for export] *)
Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148227584 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
ltac2:(KReplay.run1 (kr_t_AMallocS ()) ["CANSEC1"] "h01Hh11kh24__p1h34__x1h44__x2h54__x3h64__x4h74__x5h84__x6h92H1h:3H10h;3H11h<2H2h=2H3h>2H4h?2H5h@2H6hA2H7hB2H8hC2H9hD7__arithhE4__ffhF4__p2hG8__varmaphH5__withI4__x7hJ1qhK2q0hL1rhM2r0hN2A8hO2H0hP2M0hQ1ahR2mshS1zp%0p&0p;2p;3p;1p;4p;6p;7p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000nR1p4p710g001eR0p4p710R2p8P1p4p7210P2p8p1002Cp4p710R1p1002aR3p4p710R4p8P1P3p4p7210R3p8p1003:p4p710P2p8p1003op4p710P2p8p1004ep4p70R5P2p8P5p1005\p4p7210p8P5p1006VR6p4p710p8P5p1006mp4p73110p8P5p1007aR7p4p710p8P5p1008=p4p710p8p1008VR5p4p73101R8p10090R9p4p73110p8P8p1009IR:p4p73110p8P8p1009ep4p710p8P8p100:8R;p4p7201p8P8p100:Jp4p7201p8P8p100:\R<p4p73110p8P8p100;0R=p4p73110p8P8p100;DR>p4p73110p8P8p100;^p4p7201p8P5p4p710R8P9p4p710p8P8P:p4p710p8P8P4p8P8P3p8P8P<p4p710p8P8P=p4p710p8P8P>p4p710p8p100<1R>p4p710R8P1p8P8P4p8P8P3p8P8p100<Ep4p73110p8P>p4p741110R>P7p4p73101p8p100<Wp4p7210P2p8p100=Cp4p7<111111111110P2p8p100=ep4p741110R2P5p4p7511100R7p8P7P2p8p100>>p4p741110R2P5p4p76111100R7p8P7P2p8p100>Vp4p741110R2P5p4p771111100R7p8P7P2p8P6p4p741110R6P5p4p7:1111111100R5p8P5P6p8P;p4p7200R;P>p8P>P;p8g00D[j20Tg00?6k30<Tg00ANj11Tg00B3j1ZTg00^Jj28Tg00?kj1{Tg00@ij13Tg00BQk10;Tg00CGj22Tg00^jj26Tg00D>j2=Tg00_Gj2\Tg00E8j2VTg00_dj2kTg00`Ej1qTg00`^j2eTg00aEj2ETg00CcR;j2?Tg00aaj2dTg00bHj2cTg00bnj2bTg00ERj1HTg00cTj2oTg00d=j3YTg00F1j2nTg00dfk10:Tg00eDk209Tg00eej3XTg00Gok108Tg00Hok105Tg00IOj2WTg00]7k104Tg00JKk103Tg00Jik102Tg00M=j2jTg00RSj4^Tg00L[k100Tg00fNj6~Tg00KTj2hTg00g2j3gTg00Nfj2zTg00OHj2yTg00Obj2xTg00PNj3[Tg00Phj3wTg00QGj4vTg00R9j4iTg00gUj1uTg00hMj1|TP0j6}Tg00FZj3`Tg00GCj2tTg00HOk301Tg00Imj4sTg00S>j7mTg00L7j6rTg00Sbk706Tg00TFj8aTg00M`k307Tg00NCj3pTg00TjR0f0R>g00XmR63[p=K126>p=I%3>#3#3#3p=;%3>#3p=f%1>#1#1#1#1#1#1#1p=5%1>#1#1#1#1#1#1#Zp=Af2R5f1R2/2>'?p=B%1>#1p=l%1>#1#1#1p=U102>,25p=]%3>#1p=Nf3R7/25122>'?p=>1252/?>p=@1?2>,?5p=G1052/2>p=LA[02>p=T1n0>p=FA`02>p=DA`02>9`05p=:g00YKR8g00ZV,t2<01>p=CP0P5P2P>Csp=R1j0>p=<P2g00UHR3g00UgR4P4g00VGR1P>g00WNR=Fmp=J1h0>p=SP5P3P4P4P1P0P2g00VgP>C^P=Fmp=4P2P3P4P4P1P>Erp=_P5P3P4P4P1P2P>K06p=7P7P3P4P4P1P5P2P>Gap=MP0P2g00iFP>C^p=PB0702>p=QAp02>p=9f6R=P3P4P4P1f5R<f4R:P7P3P4P4P1P5P2P>GaGap=Op,2rcR9102>80<2g00WnR?#1R@#1RA#1RB#ZRC,85#K%I5%{9%3?RD#3RE#;#;#;RF#1#3#fRG#3#;#5#5#A&0;9R9'2S00%3FRF#;#;#5#5#ARH7B9P0g00imRI16<CRJ'0%I>%Z?RK7B>RLf7RM/0=RN%5BRB#lRO#U#5#5#5#5#5#ARP,=>RQ7]216=CRR,02RS/0C1\K>/=PRT,0MRU%NB#3#N#N#3#N#3#l#ARBP2PS%;O#;#;#;#5#AROC>3@3GX10,V0XS0g00XS%N?#U#3#f#N#U#ARS/2<RV10<:RW%1G#U#ARG3BPOP<PWP9C>%5F#ARF16MC'0RW=]NQ10WRRX/0CPBPWPXPOC>7@U5GLX10,V0P7PSP=10=<RUPGC>P;12SM12NGf9RXf8RW16XC,0FRY/0Q3L16WC,0YRZ/0C10XTPBPYPZPOC>3@5GLX10,V0S01P>12SXf:RZ/0XRY/2GP0f<R[f;R\16[CR],0FR^/0Q3L16\C,0^R_/0C10[TPBP^P_POC>3@5GLX10S02P61k\CS03%KCR_#qR^1=C]18[C'0,T[[S041e[CS051E6CR[f=R]/8CR`#I1E`C'?[S061d]CS071EC6R]f>R`/8CRa,EC?Ba6[S081c`CS09f?Ra/6C#K\_S0:1baCS0;f@Rb/8C/Tb\_S0<16bCS0=P0fARc/8CS0>P01kcCS0?fBRc16cC,=C18cC'0'T\^S0@1ecCS0AfCRc/8CR^#I1E^C'?\[S0B1dcCS0CfDRc/8CR^,EC?B^6\]S0D1ccCS0EfERc/6C#K\_S0F1bcCS0GfFR]/8C/T]\_S0H16]CS0IP0fGR]/8CS0JP0p-0R^g00Z7Rd#HRe#HRf#HRg#HRh#FRi%FgRg1o0CRj%FfRf5Y0%FeRe1n0d9Y0jRd'DRk3:Rl'D%HhRh#HRm#FRn&0:?-090Ro%FhRh5X0RpAX0oiRqAX0ogRrAY0je/Dd7:fRe'D3:1DgkRk,DiA:rfdRr,Dq9:np&088Rq'C'C'C'C&058S0K1W0:R8&0407R51W0<Rd1W0=Rf7R77R2&030S0L&020RgPgP01j06Rsg00jg%<CRtC^,JgS0M&004Ru%SERE94gsRv1_gW57gCMPuPgPgPgP3P4P4P11Pts,JgE~R4Pu%S@R3%SARA,Qt/9E'P,JgCMS0NPuPgPgP4Pu1h0?R?%SDRE,QtRw%3@#SR@'9'P,JgCMPuPg1P@s,JgPuPg19?3R3%<G54gPuPg%<S=4g?PuA4gss%<KRS94gsRx57g%<F/9ERE%<PRy,Qs'994g319EARA/9tRtAg0Ss/Qy,9?54g%<B=4gE%<ORz94gA57gRA57g57g57gFOFOFO1zg1R1P>P5g00[BR{g00[bR|'y1x>5=[{|dAw062CvR|bEbGbHX30X40X50X60X70X80W2%I=/?M\[g00kN\_R_1=C<R{/0M,T7[R}%KMAL:<G%IKRG9@6610FWR:1=6P'09L=M10:XR~/0C1\K6/=P,0=PBP:P~POC>3@3G\V[[\}[[^30^40^50^60^70^80^2^P>1E2CR}P2PWP5PXfIRVfJR~P=PMP`P]PaPbO=bDbMbKb;b:bCbBbAbLbJb@b?b>b=b<CiW9W0P2P>O2n2001000010121000000W0P>O112O=R:?BU9P;12OM12N9Q01P>12OX12Y9P0Q02PKQ03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=P0Q0>P0Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IP0Q0JP0%Hm#FRmAX0onRoA:pir3:1DhkA:pie9:moAY0ji=:hl/Cq'C'C'CQ0KAR85f1W0M9Rd77R2Q0LPgPgQ0MPu1_gX97gvCMPuPgQ0NPuPgPgP4Pu%1D#SRD,9w,P?,JgCMPuPg1_gZ%<H94g@57gPuPg1PDs,JgPuPgA4g3@PuPgA4gz?PuA4gSS97gx1QSy,9E94g3Ag0SS/Qy,9?94gt=7gA57g57gCMFOFOFOP1P|bEbGbHX30X40X50X60X70X80XI0X2^XF^%IM/?W\[10{W,T7\_R_AB\MH%KXAL<=XABGKK10FXRF1=KP'09LMW10FZRZ/0C1\KK/=P,0MPBPFPZPOC>3@3G\:[[[\_[[^30^40^50^60^70^80^I0^2^^F^P>Q00P}P2PWP9P5PXPVP~P=PMP`PcP]PaPbO@bDbMbKb;b:bCbBbAbLbJb@b?b>b=b<CiW9W0P2P>O2n2001000010121000000W0P>O1n20010000102110001100010IRRR=]UQ10RJRJ/0C10=TPBPRPJPOC>3@5GLX10,V0e%u<%|<E}bOWPWNW0XR0XQ0o"). Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6352896 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_AMallocS ()) ["CANSEC1"] "h04__x1h14__x2h21Hh31kh47__arithh54__ffh68__varmaph75__with84__x3h94__p1h:2H0h;2H1h<3H10h=2H2h>2H3h?2H4h@2H5hA2H6hB2H7hC2H8hD2H9hE2HnhF6__sat6hG1ahH1np;3p;1p;2p;4p;7p;6p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000nR1p4p710p1001ep4p710R0p8P1p4p7210P0p8p1002Cp4p710R1p1002aR2p4p710R3p8P1P2p4p7210R2p8p1003:p4p710P0p8p1003op4p710P0p8p1004ep4p70R4P0p8P4p1005\p4p7210p8P4p1006VR5p4p710p8P4p1006mp4p73110p8P4p1007aR6p4p710p8P4p1008=p4p710p8p1008VR4p4p73101R7p10090R8p4p73110p8P7p1009IR9p4p73110p8P7p1009ep4p710p8P7p100:8R:p4p7201p8P7p100:Jp4p7201p8P7p100:\R;p4p73110p8P7p100;0R<p4p73110p8P7p100;DR=p4p73110p8P7p100;^p4p7201p8P4p4p710R7P8p4p710p8P7P9p4p710p8P7P3p8P7P2p8P7P;p4p710p8P7P<p4p710p8P7P=p4p710p8p100<1R=p4p710R7P1p8P7P3p8P7P2p8P7p100<Ep4p73110p8P=p4p741110R=P6p4p73101p8p100<Wp4p7210P0p8p100=Cp4p7<111111111110P0p8p100=ep4p741110R0P4p4p7511100R6p8P6P0p8p100>>p4p741110R0P4p4p76111100R6p8P6P0p8p100>Vp4p741110R0P4p4p771111100R6p8P6P0p8P5p4p741110R5P4p4p7:1111111100R4p8P4P5p8P:p4p7200R:P=p8P=P:p8g00kkj3yTg00ANj12Tg00B3j1;Tg00CGj20Tg00?kj1oTg00@ij17Tg00BQj1^Tg00^Jj2BTg00D[j21Tg00D>j2?Tg00CcR:j28Tg00lbj2dTg00_dj2cTg00`Ej1aTg00^jj2STg00PNj3LTg00`^j2`Tg00aEj2KTg00aaj2_Tg00bHj2]Tg00bnj2\Tg00mSj2[Tg00ERj1JTg00F1j2GTg00FZj3NTg00GCj2ZTg00Goj1xTg00HOj3YTg00Hoj1wTg00]7j1vTg00IOj2XTg00Imj4HTg00JKj1uTg00Jij1tTg00KTj2PTg00L[j1rTg00NCj3MTg00nOj7qTg00Nfj2pTg00OHj2nTg00Obj2mTg00Phj3lTg00QGj4kTg00M=j2UTg00M`j3OTg00R9j4VTg00L7j6iTg00o3j4TTg00XSR=j2WTg00E8j2hTg00RSj4gTg00S>j7fTg00Sbj7sTg00TFj8eTf0R5#2#2p=D%25#2#2#2#2#2#2#2p=5%75#7#7#7p=9%75#7p=b%25#2#2#2p=@f2R4f1R0/05'8p=Eg00TjR6g00XmR77L5p=Qf3R2/041005'Wp=31805,84p=R1040/85,82p=:1075p=C1140/05p=F1005,84,82p=I1h65p=A1040/85p=61U65p==P4g00UHR3g00UgR1P1g00VGR<P6P0g00VgP5Cgg00WNFfp=4P4P3P1P1P<P0P5Fsp=>P2P3P1P1P<P4P0P5Gep=<1W05,84p=jp,2rcR;?y05g00WnR9#2R8#2R>#D#5R?#2R@#2#DRA#;RB/00RC%o;%79RD#7#9#9#9RE#2#7#bRF#7#9#2#D#@#5#5#;%^;R;'0RG%7E#9#9#2#D#@#5#5#;RE7E;P:f4RH%;?R?'B#Q10?HRI11H2RJP;PJ%@F#5#;RF%9@#9#9#9#2#D#@#5#;R@PHC3PJPB%79#2#@#9#@#5#;RJPHC37RIC:f5RI11IH%C5%;9RK7E5RLf6RM%5A#5#5#5#5#5#;RA,?5,1FRN7FI1?@5ROPMCIX36#A76;56JP41BM?#Qf7RP,0?RQ11PMRRP;PRPFP@PPC3PRPBPJPPC37RQC:P:f8RQ,0?RR11QPRPPPPFP@PQC3PPPBPJPQC37RR76;f9RR11RQPLf:RP?FRNPOPPCIX36#A76;56JP510?Pf;RR/1PRPPPPFP@PRC3P?PRPPPBPJPRC3C:76;P:f<RP/1RRR/0;PRPFP@PPC3P?PPPRPBPJPPC3C:f=RR11RPPLf>RS/1RRRPN10OSC:X36#A76;56JP510R;f?RR/1SRSPFP@PRC3P?PRPSPBPJPRC3C:P:f@R:/1RRRPFP@P:C3PRPBPJP:C396?:fARR11R:PLfBR:/1RRSPN10O:C:X36#A76;56JP5PSPFP@P:C3fCRS11S:PBPJPSC356?fDR:,0J11:SRT/0;RUPLfERV/1:RWPN10OVC:X36#ARX'81d:?%C:%C?fFRY/B?RZ#C[[1cV?%Q?R[#a1SY?,??/1Z9L6Y[1`Y?1K7?fGRZ/B?R\#C1K\?'8[1_Z?1K?7fHR\/B?R],K??E]7[1]\?fIR\/S?#Q\[1\\?fJR]/B?=L6]\[g00oN1[]?R]eP]g00YKR]g00Z7R[#JR^#JR_#JR`#J,G61G6^R^1G6_5N65N6g00ZVR_'Z%x]Ra3Y%w]RbP6%v6RcP01X64RdCH%u6Re%t6Rf%=BRg1P6DRD54f%r1RhPf%=?1P69R954fRiPfP3P1P1P<AM69D=4fg%=J=4f9RgFq5>fPhPfPiPhPgC<C<C<1pf<RgP5P4g00[BRjg00[bRk'n1m54=LjkdAl670CkRkb5b6b7X06X1610?0Rj1104Rl/0B10J03j10?410J2[[\C^06^16P5fKRCfLP\PQPRO5b410JCeb<bDbCbBbAb2bFPUPXPaPbP6PdP01X62RXCHPePf1P689M69R8=4fDRDPhPDC<PgPkb5b6b7X06X16X861150RD/0410l2[^06^16^86P5P;P:PVPMO4b4P=10TF10@:PLAFYVNPOPYCIX36#AP010WFP6PLAFZYNPOPZCIX36ROP7PaPbP6PdP0PcCHPePf%=FRd94f8PhPfPiPh1U67Ri=4fi%=KRN94fiRL5>f%=ARW9O6i9M6d94f8%=@R:=O6i=4f95>f5>fC<C<PgPkb5b6b7X06X1610DF%CKRD96771142Ri1?7A,1F1?@7/04C:\j[^06^16P5PYPZP0PPO4b4CVW2P5O110@VP6POPKp-0RO1G6`1G6[9N6^5N6/Z_=Y]aPbP6P6PXP4PcCHP0PcCHPePfPfP3P1P1P<PIEi1P6>R>%=E54f5>fPhPfA4f:9PhPfA4f8>PhA4fNN9>fLAO6NW9M6d94f8AO6:N=4f95>f5>fC<C<C<PgPkb5b6b7X06X16X86W9AE24E10@010iHAEDKK1?KA,1F9F2H1?@KP2CI[[[^06^16^86^9OP5PGP;PYPZPSP0PQO7b4CVW2P5O1n200100001021100011000CTCTW@W?P0P5O2n2001000010121000000W2W>P0P5O2n2001000010121000000W2W=P0P5O2n2011000010121000000W2W;P0P5O2n2011000010121000000b:WEW2XH6XG6o"). Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6352896 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Lemma premap_of_rt' : forall L m, arep_rt L m -> arep_rt2 m -> arep_rt3 m -> premap_cells m.
Proof.
  intros L m RT RT2 RT3.
  destruct RT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R11 & R12 & R13 & R14 & R15 & R16 & R17).
  destruct RT2 as (_ & Q2 & _).
  pose proof R11 as R11a. rw_split R11a 1%nat R11h R11t.
  unfold premap_cells. split; [exact R11h|]. split; [exact R13|]. split; [exact Q2|].
  split; [apply premap_word_212a00; exact R14|]. split; [apply premap_word_212a18; exact R15|]. split; [exact R16| exact R17].
Qed.
Lemma poison_cells_of_rt' : forall L m, arep_rt L m -> poison_cells m.
Proof.
  intros L m RT.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28).
  unfold poison_cells. repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma Z_to_bv8_bv_unsigned : forall (b : byte), Z_to_bv 8 (bv_unsigned b) = b.
Proof.
ltac2:(KReplay.run1 (kr_t_AMallocS ()) ["CANSEC1"] "h02b1h12b2h21nh31Hh41bh51zp;1p;3p;2p;6p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000nR1p4p710g001eR0p4p710R2p8P1p4p7210P2p8p1002Cp4p710R1p1002aR3p4p710R4p8P1P3p4p7210R3p8p1003:p4p710P2p8p1003op4p710P2p8p1004ep4p70R5p100ojp4p7511110p8P5P2p8P5p1005\p4p7210p8P5p1010lp4p7511110p8P5p1011bp4p710p8P5p1012Yp4p7511110p8P5p1006VR6p4p710p8P5p1006mp4p73110p8P5p1007aR7p4p710p8P5p1008=p4p710p8p1008VR5p4p73101R8p10090R9p4p73110p8P8p1009IR:p4p73110p8P8p1009ep4p710p8P8p100:8R;p4p7201p8P8p100:Jp4p7201p8P8p100:\R<p4p73110p8P8p100;0R=p4p73110p8P8p100;DR>p4p73110p8P8p100;^p4p7201p8P5p4p710R8P9p4p710p8P8P:p4p710p8P8P4p8P8P3p8P8P<p4p710p8P8P=p4p710p8P8P>p4p710p8p100<1R>p4p710R8P1p8P8P4p8P8P3p8P8p100<Ep4p73110p8P>p4p741110R>P7p4p73101p8p100<Wp4p7210P2p8p100=Cp4p7<111111111110P2p8p100=ep4p741110R2P5p4p7511100R7p8P7P2p8p100>>p4p741110R2P5p4p76111100R7p8P7P2p8p100>Vp4p741110R2P5p4p771111100R7p8P7P2p8P6p4p741110R6P5p4p7:1111111100R5p8P5P6p8P;p4p7200R;P>p8P>P;p8g00ANj13Tg013Wj1;Tg0145j11Tg00PNj32Tg014Xj20Tg015Bj3:Tg015fj29Tg016Lj25Tg0172j26Tg017ej37Tg018Qj24TP0j68Tg00Wn#3#3#3#;R0#1g019@R;f0R>#1R6f1R5#1R2g00Ccf2R7#1?25>g00TjR8f3R3/07103532R4[1075107>528%13?275[R1f4#1?237\4A:75>P>n2001000000120000000W1W0W2P1^12^06^2;P>P01005R;,90R6P5P8150;1007928>X581605970;1006140;E8O4b3W4o"). Qed.

Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem amalloc_sec : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  is_primary n = false ->
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC_of AFK) L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS bsegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until RESV. intros PRIM AHP MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK.
  assert (N : 1 <= n <= AREQMAX) by exact NR.
  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (AMALLOC_PC :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { pose proof (alayout_stack L (proj1 AHP)) as (K1 & K2 & K3).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  destruct EXARM as (trc & ARM & TRU & LTRC & SP47).
  destruct AHP as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  set (ms := sec_map_size n) in *.
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. unfold adisj in D_t_p, D_c_p.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & (kT & TBND & TBNDa & TBNDb) & (jT & TIMG & TIMGa & TIMGb)).
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (CTXi & _ & (kC & CBND & CBNDa & CBNDb)).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (NODi & _ & (kN & NBND & NBNDa & NBNDb)).
  pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (STOi & _ & (kR & SBND & SBNDa & SBNDb)).
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & (kP & OPs & OPsa & OPsb)).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & (kF & OFKs & OFKsa & OFKsb)).
  pose proof (ao_res_hi L ALO) as RHI.
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box D_t_p. box D_c_p.
  rewrite (amalloc_sec_eq RESV st n N PRIM). fold ms.
  iprefix. eapply evtF_cut.
  { eapply (malloc_pre_spec_sec L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n (al_t L) lo (al_top L) (al_bot L) tr trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- (_ /\ _) \/ (_ /\ _) => exact ARM
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0]
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 LTRC RA4 SP16;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold malloc_pre_postS in P4.
  destruct P4 as (spA & t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & s0A & s1A & s2A & s3A & s4A & s5A & s0i & fr0 & junk2 & tb & m4
                  & -> & HspA & MU4 & WM4 & MI4 & ST4 & FRa & FR16 & SS & TB & LTB & TRF & FRS & UW4).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC_of AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  pose proof AR4 as AR0. destruct AR0 as (_ & RT' & INST' & THR' & _ & _ & HS' & HD' & HRO' & RT2' & _ & RT3').
  destruct THR' as (T0' & _ & _ & _ & [sj4 [STATS' LSJ']] & _).
  destruct INST' as (I32' & I48' & I64' & I72' & I112' & I680' & I984' & I40' & I56').
  pose proof HS' as HS0. unfold AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  destruct HS0 as (WFS & ARR & INST2 & PZ & SHZ). pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  destruct INST2 as (J80 & [srt J128] & J136 & J168 & J681 & J704).
  destruct ARR as (order & PO & U64 & JK & PER).
  pose proof RT' as RT0.
  destruct RT0 as (GPG' & GOT' & GOT80' & RIC' & LS1' & REAL' & IMAX4' & FLG5' & FLG' & HPP' & SHB' & CANP' & TI' & TK' & INI2' & LAY' & MCS' & OOM3'
                    & PGC' & HK2' & CF8' & CF34' & CSMT' & T88' & TSD' & LS2' & CT8' & CT').
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct J136 as [jstats J136]. destruct J168 as [jbsl J168]. destruct J704 as [jglob J704].
  cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in J136, J168, J704.
  assert (MTX : rw_cells bsegs m4 0xb6f40 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  { apply (proj2 (rw_cells_app bsegs m4 0xb6f40 [C1 (Z_to_bv 8 0)] [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])). split; [exact I680'| exact J681]. }
  assert (JSL : exists jslot, a_nsec st < a_nres st -> rw_cells bsegs m4 (al_ptr_array L + 8 * a_nsec st) [CB 8 jslot]).
  { destruct (Z_lt_le_dec (a_nsec st) (a_nres st)) as [LT|GE].
    - destruct (junk_split m4 (al_ptr_array L + 8 * a_nsec st) 8 (8 * (a_nres st - a_nsec st) - 8)
                 ltac:(replace (8 + (8 * (a_nres st - a_nsec st) - 8)) with (8 * (a_nres st - a_nsec st)) by (clear; lia); exact JK)
                 ltac:(clear; lia) ltac:(clear -LT; lia)) as [[js J8] _].
      exists js. intros _. exact J8.
    - exists (repeat (Z_to_bv 8 0) 8). intros LT. exfalso. clear -LT GE. lia. }
  destruct JSL as [jslot JSL].
  destruct RT2' as (Q1' & Q2' & Q3').
  pose proof RT3' as RT30. destruct RT30 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R11' & R12' & _).
  pose proof R11' as R11a. rw_split R11a 1%nat R11h NAMEP. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in NAMEP.
  assert (I64x : rw_cells bsegs m4 0xb6cd8 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))]).
  { apply (proj2 (rw_cells_app bsegs m4 0xb6cd8 [C8 (Z_to_bv 64 4096)] [C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I64'|]. apply (proj2 (rw_cells_app bsegs m4 _ [C8 (Z_to_bv 64 (al_ptr_array L))] [C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I72'| exact J80]. }
  assert (LC4 : large_cells (al_ctx L) (al_t L) (al_ptr_array L) m4).
  { unfold large_cells. split; [unfold rmap_cells; split; [exact GPG'| split; [exact PGC'| split; [exact GOT'| split; [exact Q1'| exact Q2']]]]|].
    split; [eapply poison_cells_of_rt'; exact RT'|]. split; [exact NAMEP|]. split; [exact R12'|].
    split; [exact TI'|]. split; [exact TK'|]. split; [exact T88'|]. split; [exact TSD'|]. split; [exact CT'| exact I64x]. }
  assert (FROK : forall a, sfresh RESV st n a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= al_t L \/ al_t L + 4096 <= a) /\ (a + ms <= al_ctx L \/ al_ctx L + 4096 <= a) /\ (a + ms <= al_ptr_array L \/ al_ptr_array L + 8388608 <= a)
     /\ fill_at m4 (shad a) (ms / 8) 0).
  { intros a HF.
    pose proof (valid_geo L RESV st n a N PRIM HF ROK) as (AAL & AHI0 & ACE & MSP & _). fold ms in ACE, MSP.
    destruct (ablk_int _ _ AHI0) as (kA & ABND & ABNDa & ABNDb & ABNDc & ABNDd). pose proof (sec_facts n N PRIM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSBx). fold ms in MSBx.
    destruct (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]) ltac:(clear -MSBx; lia)) as (kS & ASD & ASDa & ASDb & SA1 & SA3).
    pose proof (valid_clear L RESV st n a N PRIM HF ROK) as (C_t & C_c & C_r & C_p & _). fold ms in C_t, C_c, C_p.
    unfold K_HIGH_MEM in AHI0. split; [exact AHI0|]. split; [exact ACE|]. split; [exact C_t|]. split; [clear -C_c; lia|]. split; [exact C_p|].
    unfold fill_at. apply (azero_cb m4 (shad a) (ms / 8) (ms / 8)); [| clear -MSB; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]].
    eapply (ashz_azero L _ m4 a ms SHZ); [clear -AAL; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]| exact AHI0| exact ACE| clear -MSB; lia
      | exact (valid_hulls L RESV st n a N PRIM HF ROK)| exact (valid_chunks L RESV st n a N PRIM HF ROK)]. }
  assert (TS : forall (a nres' : Z) RNG' (m1 m' : amem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    sfresh RESV st n a = true ->
    munch [(bv_unsigned sp - 2320, bv_unsigned sp - 2272)]%Z m4 m1 -> wmono bsegs m4 m1 ->
    large_post RNG (Z_to_bv 64 (bv_unsigned sp - 2320)) a n (al_ctx L) (al_t L) (al_ptr_array L) (a_nres st) (a_nsec st) nres' lo m1 RNG' m' ->
    stk bsegs m' lo (bv_unsigned sp - 2272) ->
    implS bsegs RNG' (aembed ATOP (poison0 (a + PG + rz_size n) (Z.land n (Z.lnot 7)) (aret (st_sec st nres' a ms n, Some (a_next st)))))
          (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
          (MS (mkR (Z_to_bv 64 0x31b54) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0' t1' t2'
                   (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                   (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 (al_t L)) (Z_to_bv 64 1)
                   t3' t4' t5' t6')
              F (Z_to_bv 64 0x31b54) fc None m' (seg_rom bsegs))).
  { intros a nres' RNG' m1 m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF MU1 WM1 LP STc.
    pose proof (valid_geo L RESV st n a N PRIM HF ROK) as (AAL & AHI0 & ACE & MSP & _). fold ms in ACE, MSP.
    destruct (ablk_int _ _ AHI0) as (kA & ABND & ABNDa & ABNDb & ABNDc & ABNDd). pose proof (sec_facts n N PRIM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSBx). fold ms in MSBx.
    destruct (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]) ltac:(clear -MSBx; lia)) as (kS & ASD & ASDa & ASDb & SA1 & SA3). unfold K_HIGH_MEM in AHI0.
    pose proof (valid_clear L RESV st n a N PRIM HF ROK) as VC. fold ms in VC. pose proof VC as (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d).
    unfold large_post in LP. cbv zeta in LP. fold ms in LP.
    destruct LP as (FPLE & BW & _ & _ & _ & MUL & WML & MIL & STL & HDRP & ZB & SHF1 & SHZ0 & SHF2 & RCH & RSCH & INS & SRT & JST & JBS & MTX9 & JGL
                    & [sj9 [STATS9 LSJ9]] & PAS & DISJ & NRB' & LC').
    rewrite unsigned_lit in MUL, STL by (clear -SPR LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    unfold AINSTANCE in MUL.
    assert (NR' : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells bsegs m' (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct DISJ as [D|(D1 & D2 & D3 & _)]; [left; exact D| right; split; [exact D1| split; [exact D2| exact D3]]]. }
    assert (RPA' : rng RNG' (al_ptr_array L) (8 * nres')).
    { destruct DISJ as [[_ ->]|(D1 & -> & _ & RPC)]; [eapply rng_fp_le; [exact FPLE| exact RPA]|].
      replace (8 * (a_nres st + 16384)) with (8 * a_nres st + 131072) by (clear; lia).
      apply rng_merge; [exact BW| clear -WB; lia| clear; lia| eapply rng_fp_le; [exact FPLE| exact RPA]| exact RPC]. }
    clear DISJ.
    assert (WTF : wt_facts L (bv_unsigned sp) lo a ms (a_nsec st) (a_nres st) nres').
    { unfold wt_facts. assert (NSX : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ a_nres st <= nres') by (destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia).
      repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try (clear -NSX NRB' WB LO BOT STK3; unfold AMALLOC_STACK in *; lia). }
    set (WS := ((bv_unsigned sp - 2784, bv_unsigned sp - 2272) :: (a, a + ms) :: (shad a, shad a + ms / 8) :: (748696 + 112, 748696 + 720)
                :: (al_t L + 2800, al_t L + 3168) :: (al_ptr_array L + 8 * a_nsec st, al_ptr_array L + 8 * a_nsec st + 8)
                :: (al_ptr_array L + 8 * a_nres st, al_ptr_array L + 8 * nres') :: nil)%Z).
    assert (MUS : munch WS m4 m').
    { subst WS. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUL]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
    assert (WMS : wmono bsegs m4 m') by (eapply wmono_trans; [exact WM1| exact WML]).
    assert (MUT : munch (List.filter nonempty (WT L (bv_unsigned sp) a ms (a_nsec st) (a_nres st) nres')) m4 m').
    { apply munch_filter_nonempty. eapply munch_weaken; [| exact MUS]. subst WS. unfold WT, sub_fp, AINSTANCE. cbn [outside]. clear. intros q Hq. lia. }
    pose proof (KT_rt L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT') as RTL.
    pose proof (KT_rt2 L _ lo a ms _ _ _ WTF m4 m' MUT WMS (conj Q1' (conj Q2' Q3'))) as RT2L.
    pose proof (KT_rt3 L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT3') as RT3L.
    pose proof (KT_relro L _ lo a ms _ _ _ WTF m4 m' MUT HRO') as HROL.
    pose proof (premap_of_rt' L m' RTL RT2L RT3L) as PMC.
    pose proof RTL as RT0.
    destruct RT0 as (_ & _ & _ & _ & LS1L & _ & _ & _ & FLGL & HPPL & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK2L & _ & _ & _ & _ & _ & LS2L & CT8L & _).
    pose proof HK2L as HKL. rw_split HKL 1%nat HK1L HKx. clear HKx.
    destruct LC' as (_ & PCL & _ & _ & TIL & TKL & T88L & TSDL & CTL & I64L).
    pose proof I64L as I64h. rw_split I64h 1%nat I64a I64b. clear I64b.
    assert (I32L : rw_cells bsegs m' 0xb6cb8 [C8 (Z_to_bv 64 (al_space_beg L))]).
    { eapply cells_frame; [exact I32'| exact MUT| exact WMS|]. cbn. eapply KT_img; [exact WTF| | | | |]; clear; unfold AIMG_HI, AINSTANCE; lia. }
    assert (TTL : rw_cells bsegs m' (al_t L) [C8 (Z_to_bv 64 (al_ctx L))]).
    { eapply cells_frame; [exact TTctx'| exact MUT| exact WMS|]. cbn. eapply KT_t; [exact WTF| | |]; clear; lia. }
    assert (DEPL : ADEPOT DI L m').
    { pose proof (hd_frame _ HL L m4 m' WS) as HDF. cbn [ah_depot AH] in HDF. apply HDF; [exact HD'| exact MUS| exact WMS|].
      subst WS. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p. ub DL7. ub DL8.
      repeat (apply Forall_cons; [cbn [fst snd]; intros x Hx;
        clear -Hx Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 DL1 DL2 DL4 DL5 OP WB NRB' C_n C_s D_n_p D_s_p SA1 SA3 WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; lia|]).
      apply Forall_nil. }
    subst WS.
    xport FRa MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport FR16 MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport SS MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport TB MUS WMS ltac:(rewrite LTB; clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport FRS MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport UW4 MUS WMS ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
    assert (DJSB : a + ms <= al_space_beg L \/ al_space_beg L + 137438953472 <= a) by (clear -C_r RSP; lia).
    apply (rng_fp_le _ _ _ _ FPLE) in RIMG. 
    assert (RSTK' : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE| exact RSTK]).
    assert (RCTX' : rng RNG' (al_ctx L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RCTX4]).
    assert (RT4' : rng RNG' (al_t L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RT4]).
    assert (RNO' : rng RNG' (al_nodes L) 1048576) by (eapply rng_fp_le; [exact FPLE| exact RNO]).
    assert (RSTO' : rng RNG' (al_store L) 8388608) by (eapply rng_fp_le; [exact FPLE| exact RSTO]).
    replace (a + PG + rz_size n) with (a + 6144) by (unfold PG; rewrite RZ; clear; lia).
    eapply (malloc_tail_sec DI PR L RNG' _ _ _ ra sp gp tp spA t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i F fc m' n (al_t L) a ms (a_nsec st) (al_space_beg L) lo
              (1 + Z.of_nat (length trc)) fr0 junk2 tb trc).
    all: try lazymatch goal with
         | |- forall x, _ => first [exact HROL | idtac]
         | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
         | |- stk _ _ _ _ => exact STc
         | |- bv_unsigned _ = _ => exact HspA
         | |- mem_inv _ _ => exact MIL
         | |- poison_cells _ => exact PCL
         | |- premap_cells _ => exact PMC
         | |- ADEPOT _ _ _ => exact DEPL
         | |- @eq word _ _ => first [reflexivity | exact TP | exact HspA]
         | |- @eq bool _ _ => exact PRIM
         | |- @eq nat _ _ => first [exact LTB | exact LSJ9]
         | |- u64arr _ _ _ _ => exact TB
         | |- exists sjx, _ => exists sj9; split; [exact STATS9| exact LSJ9]
         | |- map _ _ = _ => exact TRF
         | |- In _ _ => exact TRU
         | |- fill_at _ (shad _) 512 _ => exact SHF1
         | |- fill_at _ (shad _ + 512) _ 0 => exact SHZ0
         | |- fill_at _ _ _ _ => exact SHF2
         | |- rw_cells _ _ (shad _) _ => idtac
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _; CB _ _] => exact HDRP
         | |- rw_cells _ _ (_ + 4096) [CB _ _] => exact ZB
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 (al_space_beg _))] => exact I32L
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 4096)] => exact I64a
         | |- rw_cells _ _ (al_t _) _ => exact TTL
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => first [assumption | exact RCH | exact RSCH]
         | |- _ \/ _ => first [exact DJSB | exact C_t | exact C_n | exact C_s | clear -C_c; lia | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- _ = sec_map_size _ => reflexivity
         end.
    all: try lazymatch goal with
         | |- forall x, _ => idtac
         | |- _ => clear -SPR LO BOT STK3 SP47 AAL AHI0 ACE TL1 TL2 TL3 CL1 CL2 CL3 DL1 DL2 DL3 DL4 DL5 DL6 SP1 SP2 SP4 N LTRC TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd;
                unfold AIMG_HI, AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia
         end.
    all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMTS" G end.
    intros RNG5 m5 id sj5 t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d PM.
    unfold malloc_postS in PM. cbv zeta in PM.
    destruct PM as (FPLE5 & MU5 & WM5 & MI5 & ST5 & IDR & STATS5 & LSJ5 & HDR5 & PGJ5 & MAG5 & LCJ5 & AHD5 & USR5 & TLJ5 & SHF5 & SHU5 & SHT5 & DEP5 & PC5 & PMC5).
    apply implS_ret. apply evtF_done.
    pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
    xport UW4 MU5 WM5 ltac:(ub DL7; ub DL8; clear -Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 TL2 SA1 SA3 DL1 DL2 DL4 DL5 C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport INS MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport SRT MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport MTX9 MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport PAS MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; dlia).
    assert (JSTq : junk_at m5 748832 32).
    { eapply junk_frame; [exact JST| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (JBSq : junk_at m5 748864 512).
    { eapply junk_frame; [exact JBS| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (JGLq : junk_at m5 749400 16).
    { eapply junk_frame; [exact JGL| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (NR5 : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells bsegs m5 (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct NR' as [D|(D1 & D2 & ZC)]; [left; exact D| right]. split; [exact D1|]. split; [exact D2|].
      xport ZC MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB NRB' D2 C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; dlia). exact ZC. }
    assert (MUW : munch (WT L (bv_unsigned sp) a ms (a_nsec st) (a_nres st) nres') m m5).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU4]|].
      2: eapply munch_trans; [eapply munch_weaken; [| exact MUS]| eapply munch_weaken; [| exact MU5]].
      all: unfold WT, sub_fp, AINSTANCE; cbn [outside]; clear -MSB; intros q Hq; lia. }
    assert (WMW : wmono bsegs m m5). { eapply wmono_trans; [exact WM4|]. eapply wmono_trans; [exact WMS| exact WM5]. }
    assert (USR : junk_at m5 (a + 6144) (ms - 6144)).
    { replace (ms - 6144) with (Z.of_nat (cells_size [CB (Z.to_nat n) (repeat (Z_to_bv 8 190) (Z.to_nat (Z.min n 4096)) ++ repeat (Z_to_bv 8 0) (Z.to_nat n - Z.to_nat (Z.min n 4096)))]) + (ms - 6144 - n))
        by (cbn [cells_size csize]; clear -N; lia).
      apply junk_merge; [eapply junk_of_cells; exact USR5| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -N; lia); exact TLJ5| clear; lia| clear -MSR NSE RSR N; lia]. }
    destruct (store_sec DI AQ AFK HL CI CI_OK CI_OK2 L RNG RNG5 (bv_unsigned sp) lo m m5 st X LB n a nres' id sj5 RESV
                ALO ARNG0 AR BL HFK N PRIM HF ROK) as [PRES AHP5].
    all: try lazymatch goal with
         | |- fp_le _ _ => eapply fp_le_trans; [exact FPLE| exact FPLE5]
         | |- munch _ _ _ => exact MUW
         | |- wmono _ _ _ => exact WMW
         | |- u64arr _ _ _ _ => exact STATS5
         | |- ADEPOT _ _ _ => exact DEP5
         | |- junk_at _ (_ + 6144) _ => exact USR
         | |- junk_at _ _ _ => assumption
         | |- fill_at _ _ _ _ => assumption
         | |- rng _ (shad _) _ => eapply rng_fp_le; [exact FPLE5| exact RSCH]
         | |- rng _ (al_ptr_array _) _ => eapply rng_fp_le; [exact FPLE5| exact RPA']
         | |- rng _ _ _ => eapply rng_fp_le; [exact FPLE5| exact RCH]
         | |- _ \/ _ => exact NR5
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq nat _ _ => exact LSJ5
         | |- _ => clear -LO BOT STK3 SP47 IDR NRB'; unfold AMALLOC_STACK in *; lia
         end.
    all: match goal with |- amalloc_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac | |- ?G => idtac "REMST" G end.
    unfold amalloc_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE5]|].
    do 15 eexists. exists m5. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PRES|].
    cbn [fst snd]. eexists (a + 6144), _. split; [reflexivity|].
    split. { unfold ablock_range. atop_facts. pose proof (sec_facts n N PRIM) as (_ & _ & _ & RSRx & _ & NSEx & MSEx & _). fold ms in MSEx. clear -AHI0 ACE AAL N MSR NSE RSR RSRx NSEx MSEx ABND ABNDa ABNDb ABNDc ABNDd.
             split; [eapply ablk_sub; [exact AHI0| lia| lia]|]. split; [lia|]. split; [lia|]. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
    split; [exact AHP5|]. split; [exact USR5|].
    split; [eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RCH]|]; clear -N MSR NSE RSR; lia|].
    split. { eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RSCH]|]. rewrite !shad_div, shlen_div. clear -N MSR NSE RSE RSR AAL MSM. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
    intros _. unfold aptr_addr. pose proof (st_sec_fields st nres' a ms n) as (_ & _ & _ & _ & _ & _ & E7 & _). rewrite E7, lookup_insert_eq.
    cbn [chunk_user_beg]. unfold PG. rewrite RZ. clear; lia. }
  eapply (calloc_sec_spec RNG (KS RESV st n) (KS2 st n) _ (sfresh RESV st n) _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 n
            (al_ctx L) (al_t L) (a_ptr_array st) (a_nres st) (a_nsec st) lo sj4 (bv_unsigned srt) jstats jbsl jglob jslot).
  all: rewrite ?PAE.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact ST4
       | |- mem_inv _ _ => exact MI4
       | |- large_cells _ _ _ _ => exact LC4
       | |- u64arr _ _ _ _ => exact STATS'
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ'
       | |- rw_cells _ _ _ [C1 (Z_to_bv 8 (bv_unsigned _))] => rewrite Z_to_bv8_bv_unsigned; exact J128
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => exact MTX
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact I112'
       | |- rw_cells _ _ _ [CB 32 _] => exact J136
       | |- rw_cells _ _ _ [CB 512 _] => exact J168
       | |- rw_cells _ _ _ [CB 16 _] => exact J704
       | |- _ mod 16384 = 0 => exact (proj1 WR)
       | |- iclr _ _ => exact TL4 | |- AIMG_HI <= al_ctx _ => exact CL3
       | |- sclr (al_ctx _) _ => exact CL1 | |- sclr (al_t _) _ => exact TL1
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- ablk _ _ => assumption
       | |- _ \/ _ => first [ub D_t_p; clear -Y; lia | ub D_c_p; clear -Y; lia | unboxed CL5]
       | |- rng _ _ (bv_unsigned _ - _) => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- rng _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- _ => rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
              unfold AIMG_HI, AREQMAX, AMALLOC_STACK in *; clear -N LO HspA BOT STK3 SPR TL1 TL2 TL4 CL1 CL2 CL3 OP WB WR TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi OPs OPsa OPsb OPi; lia
       end.
  all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMCS" G end.
  - exact JSL.
  - exact FROK.
  -
    intros a RNG' ms' HF A0 AAL ACE LE.
    destruct (sfresh_false_cases RESV st n a HF) as [B|[E|(B1 & B2 & B3)]].
    + rewrite (KS_unr_bad RESV st n a B). apply implF_ret_unr.
    + exfalso. unfold is_err, TWO64 in E. apply Z.ltb_lt in E. atop_facts. clear -E ACE MSB. lia.
    + rewrite (KS_unr_phantom RESV st n a B1 B2 B3). apply implF_ret_unr.
  -
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HNE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HNE.
    rewrite (KS_fresh_nocommit RESV st n a HF HNE), fin_sec_nocommit. fold ms.
    eapply (TS a (a_nres st) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
  -
    intros a HF HE NRB. rewrite <- ?PAE. apply (KS_fresh_commit RESV st n a HF HE NRB).
  -
    intros a RNG' ms' HF HE OV. rewrite (KS_fresh_overflow RESV st n a HF HE OV). apply implF_ret_unr.
  -
    intros a r RNG' ms' NE R0 RCE. rewrite <- ?PAE in NE. rewrite (KS2_other st n a r NE R0 ltac:(unfold alloc_ceiling; atop_facts; exact RCE)). apply implF_ret_unr.
  -
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HE.
    pose proof LP as LP0. unfold large_post in LP0. cbv zeta in LP0.
    destruct LP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NRB' & _).
    rewrite <- ?PAE. rewrite (KS2_granted st n a) by (rewrite PAE; unfold alloc_ceiling; atop_facts; clear -OP WB NRB' OPs OPsa OPsb OPi; lia).
    rewrite fin_sec_commit. fold ms. unfold K_CHUNKS_BLOCK.
    eapply (TS a (a_nres st + 16384) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
Qed.
End S.
End CANSEC1.
