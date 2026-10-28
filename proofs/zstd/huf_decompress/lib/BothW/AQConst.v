(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import ABase.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AQConst () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2eq00c5ARocqVerifyHarness?AgentSubmission5BothW7AQConst3qszC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z01C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic9False_indI47Corelib4Init9Datatypes4bool00C56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc5ARocqVerifyHarness?AgentSubmission5BothW7AQConst6qsz_nzK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2ex00K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2ex01".
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition AQUAR_Q : Z := 0xb6f70.               (* [comment removed for export] *)
Definition AQ_MAX : Z := 0xb6fb0.                (* [comment removed for export] *)
Definition AQ_MIN : Z := 0xb6fb8.                (* [comment removed for export] *)
Definition AQ_MAXC : Z := 0xb6fc0.               (* [comment removed for export] *)
Definition AQ_MUTEX : Z := 0xb7008.              (* [comment removed for export] *)
Definition AQ_GCACHE : Z := 0xb7010.             (* [comment removed for export] *)
Definition aq_tcache (L : alayout) : Z := al_t L + 80.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AIA_BASE : Z := 0xbb500.              (* [comment removed for export] *)
Definition AIA_SIZE : Z := 0x81030.               (* [comment removed for export] *)
Definition AIA_MAP1 : Z := 0xbb508.              (* [comment removed for export] *)
Definition AIA_MAP1_LEN : Z := 0x40000.
Definition AIA_FLAG : Z := 0x149d88.              (* [comment removed for export] *)
Definition AFHOOK : Z := 0x14bdc8.                (* [comment removed for export] *)
End CANSEC1.

(* [comment removed for export] *)
Definition qsz (lst : Z) : Z := if lst =? 0 then 8 else 8192.
Arguments qsz : simpl never.
Lemma qsz_0 : qsz 0 = 8.
Proof.
ltac2:(KReplay.run1 (kr_t_AQConst ()) [] "p;1p;2g0000j10Tg000Uj12Tg0013j21Tg001Mg001k#0#0#0#2'1o"). Qed.
Lemma qsz_eq0 : forall lst, lst = 0 -> qsz lst = 8.
Proof.
ltac2:(KReplay.run1 (kr_t_AQConst ()) [] "h03lsth11Hp;3p;1p;2p;6g002Pj31Tg002jj15Tg0000j10Tg000Uj12Tg0013j24Tg003`j63Tg001MR0f0R1g004>R2510P0P2%51g001k#0#0#0#2R2510X001402f1P1E3W1W0o"). Qed.
Lemma qsz_nz : forall lst, lst <> 0 -> qsz lst = 8192.
Proof.
ltac2:(KReplay.run1 (kr_t_AQConst ()) [] "p'0h01Hh11bi001bh21ei011eh33lsth41ni021nh51ri031rp;1p;2p;3g004\j16Tg0055j2:Tg005Wj25Tg0064R0j2;Tg0000j13Tg000Uj14Tg002Pj31Tg006Wj29Tg0013j27Tg002jj18Tg001MR1f0R2g004>R331p=2%32#3p=0%22#6f1R4/:3%241543';f2/53g0076R3P0f3#2P3P1P4g001k#3#0R3#4R0%03#0#0#0#0#4R3n0100000020000=113P4f4R5#2R6A1103P5P2O1'9W2P2O1%661713W4P2O1n10210010300021010110102b1b5%84=113eW0X31o"). Qed.
Lemma qsz_pos : forall lst, 0 < lst -> qsz lst = 8192.
Proof.
ltac2:(KReplay.run1 (kr_t_AQConst ()) [] "h04__x1h11Hh27__arithh34__ffh48__varmaph55__with63lstp;2p;1p;4p;6p;8p;3p;7g007Vj2DTg0082j1CTg008Rj14Tg0092j23Tg009Pj1BTg009nj1:Tg00:Yj26Tg00;<j25Tg00;_j41Tg00<Jj17Tg00<lj68Tg00=Pj89Tg00>4j2ATg0013j2<Tg00>Vj2;Tg002Pj32Tg00?Bj3=Tg00?aj4>Tg00@Sj2?Tg00ALj7@Tf1R0g00B0R1g00BOR2P2g00BoR3f0R4g00COF@p=0g001MR5g004>R6/D4R7g00CoR8#C%481350%B5%:5R8P1P2P2P3P51656R9g00D[g001k,55R:C1,08%72P8P1P2P2P3P5P:g00EBP9C1,08E8G91A83P4f2R8g0076R3g00EiR9'<1;48=239dA=560C>b3b4b5X05A2506g00FI[\7^05P4P8P0O2b2,?0W1W6o"). Qed.
Lemma qsz_bound : forall lst, 8 <= qsz lst <= 8192.
Proof.
ltac2:(KReplay.run1 (kr_t_AQConst ()) [] "p'0h07__arithh14__ffh28__varmaph35__with41bi001bh53lstp;2p;1p;3p;4p;7g005Wj2HTg0000j13Tg000Uj16Tg00Ffj20Tg00GBj22Tg0082j1>Tg008Rj1=Tg00G]j1;Tg009Pj1:Tg009nj19Tg00:Yj27Tg00>4j2GTg0013j2FTg00>Vj2ETg002Pj3BTg00?Bj3?Tg00?aj4@Tg002jj1ATg00;_j4<Tg00ALj7CTg00H;j7DTf0R0#3#3p=1g001MR1f1R2g00H_P0C<p=4P2g00B0R3g00BOR4P4g00BoR5P0g00COFCp=5f2R6P3P4P4P5P2P0FDp=8g004>R4,H0g0076R3P3g001k#3#1R7#6R8P3P1P0P8%17#1#1#1#1#6R7n0100000020000R9'01097'2P0g00CoR9#>R:%=9R9%;1R;%:1R<%91R=1718R>/4>,5=1717R?,4>,5=R>381G=5R5P0P6g00EiR@,F31E06=B3@dA?142C@R4b1b2b310881087R2'2P0b0P:P9P;P<14??,5=98=>P5P4b1b2b31077,22P0b0n0110000020000b4%A0R0,081007'2eX51o"). Qed.
(* [comment removed for export] *)
Lemma qsz_int : forall lst, 0 <= lst -> lst < 18446744073709551616 ->
  exists z, 0 <= z <= 1 /\ qsz lst = 8 + 8184 * z /\ z <= lst /\ lst <= 18446744073709551616 * z.
Proof.
ltac2:(KReplay.run1 (kr_t_AQConst ()) [] "p'0h04__x1h11zh27__arithh34__ffh48__varmaph55__with61Eh72H0h82H1h92NEh:1bi001bh;3lsth<1ri011ri021ei031np;2p;1p;3p;4p;6p;7p;8g00Ffj20Tg0000j11Tg000Uj1<Tg007Vj2XTg0055j2VTg005Wj2GTg0064R0j2MTg00GBj23Tg00IFj1CTg00Ikj28Tg00JHj2DTg00Jej2ITg0082j1WTg008Rj1UTg0092j2TTg009Pj1STg009nj1PTg00;<j2OTg00:Yj27Tg00<Jj1NTg00K?j3>Tg00Kbj3FTg00>4j2LTg0013j2KTg00>Vj2QTg002Pj3BTg00?Bj3JTg00?aj4RTg00LEj4HTg004\j1^Tg00<lj6]Tg00;_j4ETg002jj1\Tg00ALj7[Tg00H;j7ZTg00=Pj8YTf0R1#1#1p==%11#1#1#1#1#1#1#1p=5g001MR2g004>R37B1p=?%C1#Cp=@f1R4=B21p=:f2R51341'3p=9P2P4g00EBP1CEp=AP4g00B0R6g00BOR7P7g00BoR8P1g00COF[p=2P2P4g00H_P1CEp=6P5P6P7P7P8P4P1FZp=4f3R9P6P7P7P8P5P4P1GYp=;1031R:g001kR;#1#=R<#=#5R=#1#=#5#5#5#5#5#5#<R>,X4R?1V53%?51G53'M1G93g0076R@P0f4#?%<;R0,01,3:R:P@P2P5%<<R<%<=R=n0100000020000%C;#@#@#@#@#1#=#<RA/81,D<RB':f7RC,0118>1RD,0C'3RE39X12,I2P4f5RF#?RGP21:<B=9:EX12P3g00CoRH#WRI%UHRH1T24RJ%S2RK%P2RL1O2;R;1723RM'A,2LRN%N7ROPL16M;,2LRPPO16MM,2L1720RQ,6M,2LRR54L172<RS172ART=>2M9F2S'A,2L172>RU=>2M,6;,2L94LP54L54LC;C;1LL8RMP1P5g00EiRV,K@1Q15=B@VdAJ234CRRVb3b4b5X02%?1R@103410331030RW'318A3,D<,:<1035RX18>3,05'339[[^02P1PCP4f6R5O3b2CHW6P1O1%^GP21:=B=9:EX12P0PIPHPJPKPLPLP6P7P7P8PNE]POPLP2P;g00D[PUCE,2LPOPLPPPO16QQ,2L94LR172=A>2TQ9F2S'A,2L16Q;,2LA>2UQ,6;,2L54L54L54LC;C;C;PMPVb3b4b5X02g00FI\@1000,3W18A0,D<,:=100918>0,09'339\X\?[^02P1PCP4PFP5O4b2CHW9P1O1n10210010100021110211103b:b<%\9/:B1019109D'359:X12,I2eW8W7X;2o"). Qed.
