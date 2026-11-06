(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AProg_kit Stdio_kit AHarness_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AHarness_bm () := "C46Stdlib5Lists4List2hdC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5AsanW;AHarness_bm7hinv_bmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib4LibA6Shadow8shad_divC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib5AsanW;AHarness_bm7AHBM_LOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW;AHarness_bm7AHBM_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit4appWC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib5AsanW9Stdio_kitDappW_shadow_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ShadowBshadow_bytes_munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4KENDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree6magreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib4LibA6ShadowBshadow_bytes_agreeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib5AsanW5ABase9in_rangesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5AsanW5ABase8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7in_fakeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5AsanW=AMalloc_iface;shad_unshadC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I59OSSVerify5KrLib5AsanW5ABase6ablock00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib5AsanW=AMalloc_iface:aheap_presC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW;AHarness_bm>hinv_bm_clientC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".

Section CANSEC1. Context {rc : runConstT}.
Definition AHBM_LO : Z := 0x20f80.     (* [comment removed for export] *)
Definition AHBM_HI : Z := 0x21000.

(* [comment removed for export] *)
Definition hinv_bm (m : amem) : Prop := shadow_bytes m (shad AHBM_LO) (shad AHBM_HI) (fun _ => 0).

Lemma hinv_bm_zero : forall m a, hinv_bm m -> AHBM_LO <= a < AHBM_HI -> m (wa (shad a)) = Some (Z_to_bv 8 0).
Proof.
ltac2:(KReplay.run1 (kr_t_AHarness_bm ()) ["CANSEC1"] "h01sh12H0h21zh32H1h43H11h52H6h64__p1h74__p2h84__x1h94__x2h:4__x3h;4__x4h<4__x5h=4__x6h>4__x7h?1Hh@3H10hA3H12hB3H13hC3H14hD2H2hE2H3hF2H4hG2H5hH2H7hI2H8hJ2H9hK2HahL2_HhM3_H0hN7__arithhO4__ffhP8__varmaphQ5__withR1ahS1mhT1qhU2q0hV2q1hW1rhX2r0hY2r1p&0p;1p;2p;3p;4p;6p;7p;8p-1p10000p4p710R0p8p1000Gp4p70P0p8g001>j10Tg001cj1cTg002Aj1\Tg002dj1iTg003Fk101Tg004Dj1=Tg005<j1HTg005Zj2lTg0067j2ETg006Sj1PTg007Bj2gTg007hk200Tg008Jj38Tg008dR0j2>Tg009?j1:Tg009dj2BTg00:Aj21Tg00:^j2UTg00;?j1mTg00;Xj2GTg00<5j2ATg00<Uj2TTg00=<j2?Tg00=Xj2STg00>?j2RTg00>ej2QTg00?Kj2hTg00?lj2[Tg00@Fj16Tg00@ej2fTg00ANj2eTg00B7j3dTg00B`j1~Tg00C>j2}Tg00C_j3bTg00DHj2aTg00E4j2{Tg00E`j1zTg00F@j3`Tg00F`j1vTg00G@j2NTg00G^j4XTg00H<j1uTg00HZj1tTg00IEj2JTg00Ihj1rTg00JJj6qTg00Jnj3VTg00KQj2]Tg00L4j2pTg00LVj2oTg00MBj3nTg00Maj4sTg00NSj1WTg00OLj6ZTg00Ojj3wTg00PSj6xTg00Q7j4YTg00Qbj7kTg00RFj7yTg00Rjj3jTg00SMj8|Tg00T1R1f0R2'Ep=7f3R3f2R4'Ef1R5/?2'>p=3%:2#:p=;%02#0p=^%02#0#0#0p=Cg00TOR6?821p=OA8652p=91?52,>4p=@1e62p=<Aw652p=4P5g00TmR7g00ULR8P8g00UlR9P2Exp=_1]62p=DP6P5g00VLP2CYp=KP5P7P8P8P9P2g00W3Fkp=2P4P7P8P8P9P5P2Fyp=IP6P5g00WSP2CYp=LAj652p=FP3P7P8P8P9P4P5P2G|p=5P6P5g00X:P2CYp=Mg00XaR:#0R;#0R<#0R=#0R>#0R?#0R@#c#\%c=RA#\RB#iRC[&015P0g00YFRD#=RE#7RFg00ZDRG#=RH%H;%H@'l'ER@PEP2P2PHC3RIf4RJ%P5RKO11gA1-00BRB58C[^06'>PDP4P4PGC3PJ%=3#PO1=8CB[P2f7RAPKO1=8CB\I^06,>@P0P@f8R0PKO1=8CB\I^06PDf6RLPLPGC3P0%=A#PO1=8CB[P2f;RMPKO1=8CB\I^06PDf9RDPDPGC3P5f:RG#=RIP6g00[BRB%:?#;#;#0#^#C#HR?%H=R='BRC'1RKP2%=MRNPN%:>#C#C#C#HR>#=RNC3X26P61BG=,1BROPKP2P2PNC3X26P61B>=RP,1BRQPK1BM=,1BRBPBP2C3X261U?=%O=RB#mRR1G=C1A?=RS'1,9?[1T?=1?1=RT%7S?@S=[1S?=1?=1RU1?=S1ES1'>[1R?=%OC\B1Q?=19S?\BPCP6PSP6fARS/U=fBRC1BC=,G=1AC='1'9\R1TC=fCRV/A=RW#7?@W=\T1SV=fDRW/A=RX,?=1EX1'>\U1RW=fERW/B=#O\B1QW=fFRX/A=/9X\B1BX=P6fG/A=P61U>=1G=P1A>=RX'1,9>\R1T>=%7X?@X=\T1S>=1?=X1EX1'>\U1R>=%OP\B1Q>=19X>\BPPP6PXP6f5RXg00\<1h1='[PTeRTO1%72?@2=f=PTO1%70RP?@0=PWPTO1f@RT#7?@T=p-0RTg00\bRWg00]NRU#6RR#6RY#6RZ#6R[#6R\#6R]#6#6R^#6#<%<^R^'41f6=R_1e6U5d6RU%~:,}6R`%<]R]5b6%<YRY%<R9d6_'4'4,4^'4g00]mR^'a'{%<\%<[%<Z9b6`14YU'4'4'4,4]/a^%zW5`W3`%vWP6P61N6JP41N6LCXP5P61N6XP31N6ACXCX%u6%t6RW1_WD%::R^#:R]#DRY1J6=RU'K,2W5IW%r8R`PWPWPWP7P8P8P91J61R8,LU,2WEqR7P`1J6>RZ%D^R[9V6U/FY'L,2WC5P`PW%0^#DR^,M8,2W1K^U,2W5IWP`PWPWP7P`%D<R<%D;RY9V6U/F^'L,2WC5P`PW%:;#DR;,M8,2W1_WG5IWP`PWPWP7P`1J6?R71]6:R:9V6U/F;'L,2WC5P`PW1M7<,2W1K<Z,2W5IWP`%:]#;#;#;#;#;#;#0#^#C#C#C#HR],J6R`/F:1F`YRY'M,2W1F`[,KY,2W5IWC5C5C5C5C5C5C51pW9P2P4g00^YRWg00_9R9'[1o24=8W9dAn615CsbObPbQX86X96X:6X;6X<6X=6X>6X6TW7A@AL=g00_Y\BRB1G=J/10,9>[%7A?@A=1G=X/1D,9A\Bf<R1,>P1G=L/1G,9?\BP?PDPDP>C311]A11]0R0P011]DC3[[[[[[[^86^96^:6^;6^<6^=6^>6^6T^7TP21?C=%7JPJPMPCfSPXP1PVP3PGP4PSP5fHfIO@bNb3b5b4bYbVbCbBbAb4b@bXbUbJbIbHb5bGbWbTbFbEbDb3b1PKPOPOPQC3ePN%W>EZPI%WGEZ%=?%W?EZPEPIPIPHC3eO2WKW?XM@P5P2O2n2001000000121000000W1XLFP5P2O2n2001000000121000000W1XR6WSo"). Qed.

(* [comment removed for export] *)
Lemma hinv_bm_munch : forall W m m', hinv_bm m -> munch W m m' -> appW W -> hinv_bm m'.
Proof.
ltac2:(KReplay.run1 (kr_t_AHarness_bm ()) ["CANSEC1"] "h07__arithh14__ffh28__varmaph35__with42AWh52MUh62SBh71Wh81mh92m'p;1p;3p;2p;4p;6p;9p;7g00F`j1;Tg001>j10Tg001cj16Tg002Aj1=Tg002dj1MTg003Fj1LTg00`6j3DTg00`jj1BTg004Dj18Tg00E`j1@Tg00acj1?Tg00H<j1>Tg00HZj1NTg00IEj24Tg009?j12Tg005<j15Tg00Q7j47Tg00L4j2KTg00?lj2HTg00LVj2CTg008Jj3ETg00MBj3FTg00Maj4GTg0067j23Tg00bAj6ATg00cJl9ITg00Qbj7JTf0R0#0#0p=<%00#0#0#0p=9f1R1g00Tmg00ULR2P2g00UlR2P0g00W3FJp=:%00#0#0#0#0#0#0#0p=1g00dM#;g00Xa#0#<R3#0R4#0R5#0R6#6#=%63#=#M[R3%L1f3R7f2R8;D1f4R9#Bf5R:P9P7g00YFR7#8g00ZDR9#8g00TOR;g00T1R<UP8P1P:P7P9P0g00\bR:#@R=%;:R:%?;R>%>;R?%N;R@P;14;<g00X:RA%25#2#2#2#2#0#<#9#5R5,4;C7':1K@2R2P0P8g00^YRBg00_9RC'H1C08=EBCdAF;<1CGR1b1b2b313<5P0b013<7eP=P:P>P?P;%24#9#1#5R4,4;PA%06#1#1#1#1#1#5R6,4;C7,:@P2P1b1b2b31346P0b0g00e?,39eEAM9IW4W5W6X93W8W7o"). Qed.

(* [comment removed for export] *)
Lemma hinv_bm_magree : forall (P : Z -> Prop) m m', magree asegs P m m' -> (forall a, shad AHBM_LO <= a < shad AHBM_HI -> P a) ->
  hinv_bm m -> hinv_bm m'.
Proof.
ltac2:(KReplay.run1 (kr_t_AHarness_bm ()) ["CANSEC1"] "h01sh14__x1h24__x2h34__x3h41Hh52Hah62_Hh77__arithh84__ffh96__sat1h:8__varmaph;5__with<1ah=1Ah>2AGh?1Bh@1EhA2HPhB2HshC1PhD2SBhE6__sat0hF1mhG2m'p;1p;4p;2p;3p;7p;8g001>j15Tg001cj1LTg002Aj1FTg002dj1OTg00f4j4dTg004Dj1KTg0067j21Tg00=<j24Tg008dR0j22Tg003Fj1>Tg005<j1BTg005Zj2NTg006Sj18Tg007Bj2cTg007hj2]Tg008Jj30Tg00foj2YTg00gWj3WTg00?Kj2VTg00?lj2ITg00@Fj1<Tg00ANj2:Tg00Ojj3;Tg00DHj2ETg00E`j1UTg00F@j3DTg00F`j1TTg00G@j2HTg00G^j4STg00H<j1RTg00HZj1QTg00KQj2?Tg009?j1PTg00Ihj1CTg00IEj2GTg00h;j3MTg00L4j2bTg00LVj2aTg00MBj3\Tg00Maj4[Tg00;?j16Tg00h^j7ZTg00Q7j4JTg00Qbj7XTg00RFj7^Tg00SMj8_Tg00iaj3`Tg00TOR1f1R2g00X:f0R3CJp=9P2g00TmR4g00ULR5P5g00UlR6P3g00W3FXp=3P1P2g00VLP3CJp=Af2R7P4P5P5P6P2P3F^p=@f3R8P4P5P5P6P7P2P3G_p==g00j^R4?`23p=7p-0\1g00XaR9#5R:#5#5R;#5#5#5R<#LR=#F%L;R;#FR>#OR?[R@P4P7P2P3Cdg00YF#KR4/13g00ZD#KRA,43'2RBf5RCP2O1[^<1%>8P3f4RD#>P0g00T1RE/14RF%B:RG%B<R<'NRH,1ARIf7RJ%82RKO11c;E,]>R;50?\B^01'2%>CP3f:PKO1=0?;\B^01,2IP0PIf;RLPKO1=0?;\B^01f9RM#>P3f>PKO1RN=0?;\B^01f=R;f<ROP4PAPEV1PMP;P21YG<14EGR;11E<14EH[RM[11EGRPg00kSRQAWG<2UW511EH\Q^5PP2g00\<1VEG'IP;eO1PMg00\bRMg00]NR;#<RP#<RQ#<R<,:11:1Q1:1;R;5;15;1g00]mRQ'E%<<,:11:1P=;1;5;1/EQ%UMRQ5DM3D%TMRMP11H17P21H18CSR;%R1RP%Q1R<1?1:R:1?19RR'9,3<%P9,?1R9,AR,3<5@<%C5R5P<1G1G=M1=R=,99,3<P5P<1G1ERG/9:,3<P519GR,3<1AR=,3<5@<C=C=C=1b<6R6P3P7g00^YR=g00_9RG'I1a37=0=GdA\1E2C[RGb8b:b;X11X21X3111231437'2118H11E8RE148H,2E[[[^11^21^31P3PAP4PCPDPJPLO6b7b9bEb9POP2PQPMP;PPP<19R:,3<1A:9,3<5@<R<P5P<C=P6PGb8b:b;X11X21X3111321427'211271478'2[^11^21^31P3PAP7P4P2O4b7O2O3f?R4PKO190?N174K%C>R>50?#6%87R7,74=0?>#6['2P0P4P7O1f@R4P7O150?1747=0?>#6%88R8,74=0?>#6[P4P8O1fAR4P8O150?P3P4%8DRDO1fBPDO150?fCRD%8C'7=0?>#6f6#8,7D=0?>#6[P2W6W@P2P3O2n2001000000120000000b<XBBX01FZW6X?IP2P3O2n2001000000121000000W4X=FP2P3O2n2001000000121000000b4WDWAW>XG@WFWCo"). Qed.

(* [comment removed for export] *)
Lemma hinv_bm_client : forall CI LB SP a, (forall x, AHBM_LO <= x < AHBM_HI -> in_ranges CI x) ->
  shad AHBM_LO <= a < shad AHBM_HI -> aclient_addr CI LB SP a.
Proof.
ltac2:(KReplay.run1 (kr_t_AHarness_bm ()) ["CANSEC1"] "h02Hah12H0h22H6h34__p1h44__p2h54__x1h64__x2h74__x3h84__x4h94__x5h:1zh;2CIh<1Hh=2H1h>3H10h?2H2h@2H3hA2H4hB2H5hC2H7hD2H8hE2H9hF3HCIhG3Ha'hH2LBhI2SPhJ7__arithhK4__ffhL6__sat0hM6__sat1hN8__varmaphO5__withP1ahQ2a'hR1xp&0p;2p;1p;6p;3p;4p;7p;8g00kok209Tg00F`j1STg00lOj2GTg004Dj1>Tg001>j11Tg009?j1;Tg005<j1?Tg009dj2TTg00:Aj26Tg00NSj1gTg00mIj6cTg00mej2_Tg00:^j2\Tg00;?k100Tg00;Xj23Tg00<5j2ZTg00<Uj2YTg00=<j28Tg008dj29Tg00=Xj2[Tg0067j2ITg00>?j2]Tg00>ej2`Tg00nVj2WTg00?Kj2lTg00?lj2UTg00@Fj1@Tg00ANj2BTg00B`j1kTg00C>j2jTg00C_j3iTg00@ej2hTg00B7k308Tg00DHj2fTg00E4j2dTg00E`k107Tg00F@j3bTg00G@j2aTg00ack106Tg00G^j4QTg00H<k105Tg00HZk104Tg00KQj2DTg00IEj2ETg00Ihk103Tg00JJj6~Tg00Jnj3KTg00Rjj3FTg00oRj3{Tg00L4j2zTg00LVj2yTg008Jj3MTg00MBj3xTg00Maj4wTg0105j2CTg005Zj2vTg010Rj2uTg011Kj1tTg012Aj2eTg0139j2ATg013Sj2sTg013mj3rTg014Gj3HTg014aj1qTg015ej4|Tg016Aj4}Tg016\j4pTg00Ojk301Tg00PSk602Tg00Q7j4LTg00Qbj7oTg00RFj7nTg00SMj8mTf3R0f2R1'If1R2f0R3'8'9p=0%;3#;p=2%13#1p=X%13#1#1#1p=:g00T1R4/I3p=5g00TOR5?M34p=PAM523p=71823,91p=VB01523p==P2g00TmR6g00ULR7P7g00UlR8P3J02p=^P5P2g00VLP3CLp=RP2P6P7P7P8P3g00W3Fop=4P1P6P7P7P8P2P3Fnp=JP5P2g00WSP3CLp=OP0P6P7P7P8P1P2P3Gmp=<P5P2g00X:P3CLp=N20955#Sg0176#Sg00YFR9P3P3g00ZDR:C0f5R;/G2[^R5%>9P2P2%>:C0P5g00XaR<#1R=#1R>#1R?#1R@#1#;#2#2#1#X#:#?RA#>P3P0P0%;@#:#:#:#?R@#>RBC0X:5P3g00[BRC%??R?,TARD'6RE%gAEcPEP1P1PBC0P5PBPEf4RBPBP3C0X:5P31T@?RF,6CRG%g@EcPEP0P0PGC01_A?%5A%5?RG%5D[[1_@?%5@%5F\G[1\@?%P?RG$00RE13?F1Z@?RH'6,7@[1Y@?184?RI%5H18H?RJ'9RK[1[@?18?4RL18?H1IH4'9[1]@?%PF\G1`@?17H@\Gg017oRM1W@?RNePN1\A?13?D1ZA?RN'6,7A\E1YA?%5NRE?VN?RO\I1[A?18?N1IN4'9\L1]A?%PD\G1`A?17NA\GPM1WA?RMePMPBg00\<1l4?'UPIeRIO1POf;PIO1PKp-0RKg00\bRIg00]NRO#@RM#@#@RL#@RP,B5RQ%k<,j51B5L5i51h5?1B5MRM60851B5ORO'='='=g00]mRL'f%@PRP#@,B51B5P'=1=OQ,=M/fL,dM'd&07I5bI3b%SIP5P51a5BP1&065RICQP2P51a5;P0PICQCQ&055&045RIf7RM,^I%;=RL,D5RO1E5?RQ'R,4I5JI&037RPPIPIPIP6P7P7P81E54R7,OQ,4IE~R6PP1E5ARR1D5=RS9K5Q=F5O'O,4IC<PPPI1D5>R>,N7,4If8R7,^I5JIPPPIPIP6PP1E5@R6%;<RO,D5RT9K5Q=F5>'O,4IC<PPPI%2O#2#2#2#2#2#2#1#X#:#:#:#?RO,E5R>=F5S1D5<R<'N,4IAF5>T,R<,4I5JIPPA{5<>9K5QRQ,NR,4I1RQ6,4I5JIC<C<C<C<C<1zI8P3P1g00^YRIg00_9R8'U1y31=MI8dAx542CwbKbNbOX55X65X75X85X95X3KW4AV;B?g00_Y\GRG13?0f6R4'6,7A[%5;/9713?4/6M,7@\G16O;PBPB16O4C0PA1C;O,3?RGPGP@C0[[[[[^55^65^75^85^95^3K^4KP3PJPEPNPHPFPDfEP1P7P2f>fAO<bJb1b2PAfB/CO,3?ROPOP@C0eb>bEbDbCb2bBbAb@b?b=b1b<bLbMPA1CBC,3?RAPAP@C0eb0b0P91C1C,3?R9P9P:C0R:eP:PBP0P0%?=%;L#2#?'vRLC01G40R=1u;0R:p,2rc#tR9P3P3PLC01GM31e43'A'A%>3,7B'9XQ5RB,s5RM'AR@'AP5PB1C0C,3?R?P9P?P?PLC0RL1G4?R41e;?R;'AR9'A%>?RC,70P1P?P3O29r4;9HL9P5PCP0%q0C|C}Cp9H:M9H=@3HbGW0WFXP5XI5WHW;o"). Qed.

(* [comment removed for export] *)
Lemma hinv_bm_pres : forall CI LB SP m m', aheap_pres CI LB SP m m' -> (forall a, AHBM_LO <= a < AHBM_HI -> in_ranges CI a) ->
  hinv_bm m -> hinv_bm m'.
Proof.
ltac2:(KReplay.run1 (kr_t_AHarness_bm ()) ["CANSEC1"] "h01sh11Hh22Hah32_Hh46__sat1h54__x1h64__x2h74__x3h81ah91Ah:2APh;1Bh<2CIh=1Eh>3HCIh?2Hsh@2LBhA2SBhB2SPhC7__arithhD4__ffhE6__sat0hF8__varmaphG5__withH1mhI2m'p;2p;1p;6p;3p;4p;7p;8g00koj2fTg00F`j1ATg001>j14Tg001cj1CTg002Aj1LTg002dj1YTg018Kj6VTg0067j21Tg00=<j26Tg008dR0j22Tg00lOj2PTg003Fj1=Tg004Dj1BTg005<j1ITg005Zj2dTg006Sj17Tg007Bj2XTg007hj2WTg008Jj30Tg00foj2UTg00gWj3TTg00?Kj2STg00?lj2FTg00@Fj1<Tg00ANj29Tg00Ojj3:Tg00DHj2ETg00E`j1RTg00F@j3DTg00G@j2JTg00G^j4QTg00H<j1OTg00HZj1NTg00KQj2>Tg009?j1MTg00Q7j4?Tg00Ihj1HTg00IEj2KTg00h;j3eTg00L4j2cTg00LVj2bTg00MBj3\Tg00Maj4ZTg019Nj6[Tg00;?j13Tg00h^j7]Tg00Qbj7^Tg00RFj7_Tg00SMj8`Tg00iaj3aTg00TOR1f1R2g00X:f0R3C?p=;P2g00TmR4g00ULR5P5g00UlR6P3g00W3F^p=8f2R7P4P5P5P6P2P3F_p=Gf3R8P4P5P5P6P7P2P3G`p=@g00j^?a23p=51f11#Ag0176#Ag00XaR4#4R9#4#4R:#4#4#4R;#CR<#L%C:R:#LR=#YR>[R?p,2rcf4R@P8P7P2P3EVg00YFRA/13g00ZDRB,63'2f7RC/P2[^81%=8P3%=@P0g00T1RD%BARA'1RE%BBRB%I9RF%I;R;'dRG'1RH11A3163B'2RIPC%72RJO11X:D,W=R:50>[^01'2f5RK#=P3f:PJO1=0>:\I^01,2HP0PHf;RLPJO1=0>:\I^01f9RM#=P3f>PJO1RN=0>:\I^01f=R:f<ROPAPBPDV1PMP:P21UF;16DFR:11D;16DG[RM[11DFRPg00kSRQATF;2UW211DG\Q^2PP2g00\<1SDF'FP:eO1PMg00\bRMg00]NR:#<RP#<RQ#<R;,91191Q191:R:5:15:1g00]mRQ'E%<;,91191P=:1:5:1/EQ%RM5DM3D%AMP11J17P21J18CQ%O1%N1RM1>19R91>14RQ';,8MP1PQg00VLR:%M4,>1R4C?,8M5GM%H5R5PM1K1F=e1<R<,;4,8MP5PM1K1DR4/;9,8MP51;4Q,8MP1PQP:P<C?,8M5GMC@C@C@1cM6P3P7g00^YRMg00_9R6'F1b37=0M6dA\1D2CZbDbFbGX51X61X7111231637'2118G11D8RD168G,2D[[[^51^61^71P3PBPAPKP@PCPLO6bCb4bEb4fBRLfARCf@RAP2POP3E[O3f?ROPJO190>N15OJ%H=R=50>#3%77R7,5O=0>=#3['2P0POP7O1PAP7O150>15A7=0>=#3%78R8,5A=0>=#3[PAP8O1PCP8O150>P3PC%7@R@O1PLP@O150>fCR@%7K'5=0>=#3f6#7,5@=0>=#3[P2W3W=P2P3O2n2001000000120000000b8X?IX01F]W3X;HP2P3O2n2001000000121000000W1X9EP2P3O2n2001000000121000000b1WAW>W:XI?WHXB1W@W<o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FuzzOneB.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Definition fuzz_oneA_stmtB : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (D : Z) (payload : list Z) (lo : Z) (rstk : region),
      AHEAP AI L RNG (aps_m s) LB m ->
      (* [comment removed for export] *)
      (forall b, In b LB -> exists p A n, b = HB p A n) ->
      (* [comment removed for export] *)
      payload_atA LB D payload ->
      bytes_at asegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      D mod 16 = 0 -> zlength payload < 2^26 ->
      (* [comment removed for export] *)
      harness_invA m ->
      (* [comment removed for export] *)
      hinv_bm m ->
      (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK ->
      bv_unsigned sp + ATRUN_DEPTH = al_sp0 L -> bv_unsigned sp mod 16 = 0 ->
      (* [comment removed for export] *)
      rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
      s0 = Z_to_bv 64 (zlength payload) ->
      mem_inv asegs m -> frm0 fc ->
      tp = Z_to_bv 64 ATP ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) -> ra = Z_to_bv 64 ATRUN_RET ->
      (* [comment removed for export] *)
      HU L ->
      (* [comment removed for export] *)
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
      (* [comment removed for export] *)
      aps_ok L s ->
      implMA RNG (fuzz_oneA AAllocAsan payload) s
             (fuzz_oneA_post AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom asegs)).
End FuzzOneB.
End CANSEC1.
