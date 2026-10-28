(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_bdt_lp RF_huf_tbl_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_rs_cl.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_bdt_kit () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3sxbI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface7zshadowC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission4LibA6ShadowCrw_cells_C1_of_byteK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells7cell_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step=rw_cells_readC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z6shiftrK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5nshadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow9nshad_divC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init9Datatypes3nat00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW5ABase>ablk_disj_bandI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlc5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit>app_vs_shadowZI47Corelib4Init9Datatypes4prod00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp<lowprob_loopK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model;bind_Ok_invI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model7load_OkC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6ostoreC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC47Corelib4Init9Datatypes7nat_indC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega;ZifyClasses5mkrelC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp3u16C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount8to_shortC56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission5Plain@RF_huf_bdt_model4tsymC47Corelib4Init3Nat3mulI47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sC47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3addC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List<length_skipnC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit;u16s_lengthC46Stdlib5Lists4List:length_appc5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_bdt_kit3wkbC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_bdt_lp:snext_snocC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem9upd_bytes".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma sxb0 : sxb (Z_to_bv 8 0) = Z_to_bv 64 0.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_kit ()) [] "p;1p;2p;3g0000j10Tg000Uj12Tg0013j14Tg001Vj23Tg002Ij38Tg002lj27Tg003Fj21Tg003lj15Tg004\j36Tg0056#0#0#0R0#0#0#0#2R1#4R2g005[R31313581'7%20/13#51113562do"). Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma chkZ : forall m X n a, zshadow m X n -> X <= a < X + n -> 0 <= a < 2^47 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_kit ()) ["CANSEC1"] "h02Hah14__x1h22RDh31zh41Hh57__arithh64__ffh78__varmaph85__with94__x2h:4__x3h;1Eh<2H0h=2H1h>2H2h?2H3h@2HbhA1RhB2S0hC1XhD2Z0hE6__sat4hF6__sat5hG6__sat6hH6__sat7hI1ahJ1mhK1nhL1qhM1rp&0p;1p;3p;2p;4p;6p;7p;8g0000j1DTg000Uj1NTg0013j1QTg0069j1MTg006[k303Tg007^j27Tg008:j20Tg008Wj23Tg0093j24Tg009Nj19Tg009lj1CTg00:Qj2\Tg00:nj1BTg00;fj1<Tg003Fk200Tg00<Uj2XTg004\j31Tg00=7j2FTg00=Tj2rTg00>5j1nTg00>Nj2TTg00>kj2@Tg00?Kj2iTg00@2j2gTg00@Yj2fTg00A?j2eTg00Aej2STg00BMj3RTg00C1j1>Tg00CPj2:Tg00D9j1cTg00DWj2bTg00E8j3aTg00Eaj2`Tg00FJj3_Tg00G3j2PTg00G_j1^Tg00H?j3OTg00H_j1]Tg00I?k107Tg00I]j2[Tg00J;j4ZTg00JYk106Tg00K7k105Tg00Kbj2=Tg00LEk102Tg00Lgj2KTg00MJj6}Tg00Mnj3yTg00NQj3GTg00O4j3WTg00OWj2xTg002lj2VTg00P9j2wTg00Pej3qTg00QDj4pTg00R6j1oTg00Roj6UTg00SMj3mTg00Shj3lTg00TCj7kTg00UGj1sTg00V<j4tTg00W2j2jTg00Whj8uTg00Xcj1vTg00YCj1hTg00Z7j4?Tg00[<j1zTg00\1j1{Tg00\Rj6|Tg00\nj2YTg00]Nj3~Tg00^7j4JTg00^bk701Tg00_Fj7dTg00_jk804Tf0R0#D#Dp=6g005[R1/70p=2%C0#Cp=8g00`NR2f1R3;~0p=;P2P3g00`lP0CJp=LP3g00aSR4g00b2R5P5g00bRR6P0g00c2K01p=5P2P3g00cRP0CJp=Ef2R7P4P5P5P6P3P0Fdp=Hf3R8P4P5P5P6P7P3P0L04p=AP2P3g00d9P0CJp=Ig0056R9#DR:#6R;#D#6R<#NR=#Q%N;R>#QR?#MR@[B0387317831087,33'4%27%9:RA%C:R:#C#8RB#9RC'\RD,37'4P7P8P3O2f6RE%B8#<O1200>1R>,X?51@P2g00d`f4R@%9;R;'F'0RF%20%99RG,00%9<R<,\ARH'7'4X321r@;A12;1RI#nf5RJ1FJ;,T;1@J;'0512[1iJ;131;RK1@E;RL#213L;'4[1gE;13;1f7RL/@;RM,3;17M1'4[1fL;f8RM/F;=121\I1eM;f9RN/@;=12N\I1FN;P2f:RO/@;P21SAC131ARP%2C131D[[%2ARQg00eZRRARAC3UW0%2D\R^0Q1SA<%2<131H[\PARA<3VRX0Q%2H\R^0Qg00f6RQg00fbRR#>R<#>RP#>RC#>RS#>,:2%c9,b21:2CRC5a21:2<1`2;1:2R5_2R<';';';g00gART'P1:2S1:2P/;<,;C';/PT%^QRT5OQ3O%]QRQP2&072RCP3P21[28P7PCCZCZ&062RC&052R<P<1=21RP1=2;RS'L,5<&025RU1K2:R:,EP,5<1L:S,5<5H<CAPUP<P<P<P4P5P5P61ISP,5<E}PU%C9R5,K2R41K29R99y2S=G2:'I,5<CAPUP<1EP4,5<1=2ARA%NB5W2,L4,5<5H<PU%85#8#8#8#8#8#8#D#6#6#6#6#6#6#6#9RU,=2R4=G29RB,EP,5<1=2G9G2BAW2A='E,5<5H<CACACA1x<6R6P0P7g00gmRAg00hMR='V1w07=1A=dAq213CpR=b6b7b8X12X92X:2%28RA138;'4\Kg00hm\I1T;7/0@9128[138D,4A10U8R8#2108G/7H'4[[[^12^92^:2P0PJf@PEPOf;R8f=RAO6b5bEbFbGbHbMbLb?b>b=b<b4%2F10FG/7H'4e%B@RF%o@EU%2F10FG/7H'4g00iJRFPM%BJRJP>%2JR@10JG/7HRH;m0Al@H0P3FkPFPMPJg00j?RJ%s>R>%^J3ORHCtPFPN%BEREPHPRP>P0%MJ1jHR'VGu%]?R?#MRHPFPN%vR,0E#<%h>REC?%z>,X?R?31P2%BLRL/01PFP8%<0R8PEC?=1H?X32P0PL%{LE|PFPO%<LPEC?=1H?PTPQ1[23PCAG294/IB,5<P6P=b6b7b8X12100U10U0512^12P0%95R5,YNRNO1b51YM5R5/0U10U5512P210UNPFPAP8PEC?=1H?X32P310NURNP0EUPFf<%<NPEC?=1H?P0b2b4b2b2bAbBb;W@W0WDXI2XK2XC2WJo"). Qed.

(* [comment removed for export] *)
Lemma acc_shZ : forall RNG A len a, rng RNG (shad A) (nshad (len + A mod 8)) ->
  (0 <= A /\ A <= a /\ a < A + len /\ A + len + 8 <= 2^47) ->
  acc_in RNG (Z_to_bv 64 (Z.shiftr a 3 + 2147450880), 1%nat).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_kit ()) ["CANSEC1"] "h02H2h11bh21jh31zh44__x1h54__x2h64__x3h74__x4h84__x5h92Hah:7__arithh;4__ffh<4__p1h=4__p2h>8__varmaph?5__with@4__x6hA1HhB2H1hC3H10hD3H11hE3H12hF3H13hG3H14hH3H15hI3H16hJ2H3hK2H4hL2H5hM2H6hN2H7hO2H8hP2H9hQ7__sat17hR7__sat18hS7__sat19hT7__sat20hU1qhV2q0hW2q1hX1rhY2r0hZ2r1h[2H0h\4__x7h]4__x8h^4__x9h_1Ah`2HAha2HLhb3Ha1hc3Ha2hd3RNGhe1ahf3lenp%0p&0p;1p;2p;3p;6p;4p;7p;8g00:nj18Tg0000j1ETg009Nj1BTg00>kj22Tg00k4k30NTg00:Qj2lTg007^j21Tg00Xck103Tg008:j20Tg0093R0j2NTg008Wj24Tg009lj1DTg000Uj1xTg0013k10@Tg00\nj2LTg00C1j1JTg00kgj2TTg00l]j1eTg00=7j23Tg00R6j1qTg00\Rj6_Tg00mSj1yTg00nMj2cTg00=Tj2PTg00>5k100Tg00?Kj2[Tg00@2j2ZTg00@Yj2XTg00A?j2QTg00Aej2~Tg00BMj3}Tg00D9k10MTg00DWk20LTg00E8j3|Tg00Eak20KTg00CPj2{Tg00FJk30JTg00G3j2gTg00G_k10GTg00H?j3fTg00H_k10FTg00I?k10ETg00JYk10DTg00K7k10CTg00Kbj2wTg00LEk10?Tg00MJk60>Tg00Mnj3pTg00Lgj2uTg00OWk20=Tg002lk20<Tg00P9k20;Tg004\j3\Tg00Pek30:Tg00QDk409Tg00>Nj2sTg003Fj2tTg00O4j3rTg00o7k207Tg00Roj6vTg0103k306Tg010\k305Tg0119k30ATg011Vk404Tg00]Nj3mTg00I]k20BTg00J;k402Tg00^7j4nTg00^bj7zTg0126k601Tg00_Fk70HTg00NQk30ITg00_jj8`Tf1R1f0R2'0#ep=ag005[R3/12p=7%E2#Ep=Af2R4/01/12p=51212,04p=b%e2,01p=h%D2#Dp=O1N12,N4p=]1131/N2p=:1012,t4p=IP4g012ZR5P1P2H04p=R1441/N2p=@g00d`/02p=?1041/02p=6g00`NR6?\23p=Kf3R71s41/025\6p=>1123p=YA\612p=C1{62p=MAm612p=oAm6129m64p=^20B62p=FP6P4P1P2H02p=;1w62p=VP6P1g00`lP2Cnp=SP1g00aSR8g00b2R9P9g00bRR:P2g00c2R;Fzp=<P1P8P9P9P:P2J01p=d1u62p=HP4P8P9P9P:P1P2K0Hp=UP6P1g00d9P2Cnp=WB0I612p=9P4P8P9P9P:P6P1g00cRP2CnP;Fzp=GP7P8P9P9P:P4P1P2G`p=if6R;P8P9P9P:f5R<P8P9P9P:f4R=P7P4G`P1P2G`p==1412,N4p=j10129\64p>08P;P8P9P9P:P<P=P7P8P9P9P:P4P1P2G`G`p=kg0139%84g0056R>#ER?#ER@#ERA#BRB,24,a160N7P0%87RC#7127B,a4%B?RD%EA#ARE#BRF'lRG55C%8<RC/11&031,04RH%8;Ab<;B'hRI'1f8RJP7P4O2[[^25^16'N11=410=7RK,44%D?RL#D#OS00#BRM,lDRN95KB3],:=%xERE$0@RK%D>RO#BRP,L7%DORQ#D#O#O#O#O#O#O#E#A#A#A#A#A#A#A#BRR5IEg00fbRS#JRT3R,T;[P2%7C11IG%8J/11f9RI#8RCAbJIB'hRU,1Hf;RVP7P4O2[[^25^16'NP0f7RW#812WB,a;;5G11C1f:RC#8AbICB'h,1Hf<RXP7P4O2[[^25^1611J;10JWRY,4;A5YBN3],:J1LWP=IER=RKT,TC[P211UG%8X/11f=RU#8AbXUB'h,1Hf?RYP7P4O2[[^25^1611VI10VCRZ,4IA5ZBN3],:VP0%7XS0111XC10XVRZ,4CA5ZBN3]f>RZ1LVP=IER=RKT'TP2%7Z11YU10YZR[,4UA5[BN3]P0f@R[/1Z10[YR\A5\BN5@ZfBR\1LYP=IER=RKT'TP211\[fAS02fCR[/0\R]A5]BN3@P0fDR0/0[R],4\A5]BNfFR]1L[P=IER=RKT'TP2fE,0],40fG/0]?5BNP6fHR^#81141fKR_fLR`/2BS03'0Ra#eRb,07,1HfNRcP7P4O2[[^25^16X36PU13^B#?%q^E_fJRd/3B#?Re/1113_BRf#?Abd_BRg#eRh'0,1HfMRiP7P4O2[[^25^16P6fIRj#812dB,aj=52GX36PY13jB#?RY%qjE_12jB,a^=5YGP6%8d%72X36P0Pe%qdE_%7eP6Ph13cBRh#?Re/11fORd/3BS04#?/07,1HfQRYP7P4O2[[^25^16X36P4%BQRk,0g/3B%ygE_13iB#?Rg/1112cBRl=6ik/3B,0e,1HfPRHP7P4O2[[^25^16P6PbA5g2GX36P410ak/3BRg%yaE_13`BS05#??5gGP61lDP,3_PdAIE2R,cEPTO2X36P610fRRfPdP2PTO2X36P1PfPT1PiB%KBRg$00RaPcPBPhPlC>[1[cB143BRh12dBRb14bB':[1ZdB14B3Rb12HBRe%Ye5@B[1XHB13YB#K\g1QYBfRRm/2B/Cm\g13mBP6fSRn/2BRoP61PmBPnPB13nBPoC>\a1[nBfTRn/2BRo14oB':\h1ZnBfURo/2BS06Q06#Y5@B\b1XoBfVRm/3B#K\g1QmBfWRp/2BRq/Cp\g13pBP6fXRr/2BP6fZRs?6Wk/PBf[S07?6JkRtPB13tB12tBC>\a1[tBf\S08?6IkRt/2BRu14uB':\h1ZtBf]S09?6CkRt/2BRu%Yu5@B\b1XtBf^S0:?6VkRt/3B#K\g1QtBf_S0;?6XkRt/2B/Ct\g13tBP6f`S0<?6Uk/2BP61~DMS0=143DRt%7M143N[[S0>%7DRug00eZRvA}DM1UW9S0?%7N\v^9uS0@1~DFS0A%7F143G[\tS0BA}DF1VvX9uS0C%7G\v^9uS0Dp-0Rug00f6Rv%JTRF#JRt#JRM#JS0E#MRw%MMS0F%MtS0G&0M>-0L6S0H%MFS0I5|6%MT20K6B1{6S60J6S0J'oS0K3^3^S0Lg00gARS'g&0GvRF3f&0FvS0M%F;S0N&0E6Rt7;7?;4t%F=S0O%F<S0P7;;7;1&0D6S0Q&0C6RMPM1w63Rx%VBRy'S,<MRz&0?9R{1dMJ%HARA/Sy,<M5UMP{PMPMPMP8P9P9P:1Wyx,<MJ0>R9P{%HLRL%H?R?9p6y/9AS0R'W,<MP{PMPMPzP{%HQRQ9GMxR81dMI5UMP{PMPMP9P{%H@R|1u6>R}9p6y/9QS0S'W,<MP{PMAGM|LS0TP{%VRR~/9}19?~5GMCiF=F=F=F=20=M:S0UP2P4g00gmS0Vg00hMR:+0<Q0V20;24;\:dB0:631H09S0Vb;b>b?X46X56X66X76X86X@6X<uW=AjW;B\hg00hm\gR3P<PBP7PWC>[1:WC\h1sB=S0W>08;J\311;W10;RR:95R<[[[[[^46^56^66^76^86^@6^<u^=uP214[BS0XQ01PXP[feS01fgS0YPUP0Q02P\P^PjPnO=b:bQbRbSbTbZbWbIbHbGbFbEbYbVbDbCbPbObNbXbUbMbLbKbJb01P_BS02P`PBQ05Q03C>\aS031[`BS0512iBR`14`B':\hS0Z1ZiBS0[%Yl9@Bl\bS0\1XcBS0]Q04#K\gS041QdBS0^1CeH\gS0_13HBS0`P612YBS0aP61PnBS0bPoPB13oBQ06C>\aS061[oBS0c12mBRo14oB':\hS0d1ZmBS0e%Yq9@Bq\bS0f1XpBS0g13rB#K\gS0h1QrBS0ifYRp/2B/Cp\gS0j13pBS0kP612sBS0lP6A6s2k/PBS0mQ07?61kRsPB13sB12sBC>\aS071[sBRsQ08?64kRa/2BRp14pB':\hRp1ZaBRaQ09?67kRq/2BRm%Ym5@B\bRb1XqBRqQ0:?6=kRm/3B#K\gRo1QmBRmQ0;?6<kRY/2B/CY\gRg13YBRYP6Q0<?6;k/2BReP6Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0E#JRl#MRiQ0L'o/gS=fvFQ0M%FJ?;=tQ0N7;4%FI?;<t%FW7;77;1Q0QPMPMPzP{1dMV%D@#HR@/Sy,<M5UMP{PMPMP9P{%EO#HR`/9A%Vk'9%HORO9p6y/9@'W,<MP{PMPMP9P{Q0R,W|,<MP{PMPMPzP{1dMX9UM8P{PMPMP9P{Q0S,WL,<MCiR9P{PM19|`R`,SL,<MRLP{19}~R}%B>R>#V'919~?/9O5GMFkF=F=F=F=Q0UQ0Vb;b>b?X46X56X66X76X86X@6X\6X]6X^6X<uX=uAjCIB\hA6WIkQ0W/0CRk'C\31C;k\31:CZ\hPIPBP<PVC>\310JC,4IA6RWJ95:>[[[[[[^46^56^66^76^86^@6^\6^]6^^6^<u^=uP2Q0X%7<RuP<PXP[ffRXQ01Q0YP;PUP0PCPVP\P^PjPHOAb:bQbRbSbTbZbWbIbHbGbFbEbYbVbDbCbPbObNbXbUbMbLbKbJb0O41tEf,cEQ02Q03Q05Q0ZQ0[Q0\Q0]Q04Q0^Q0_Q0`P6Q0aP6Q0bQ06Q0cQ0dQ0eQ0fQ0gQ0hQ0iQ0jQ0kP6Q0lP6Q0mQ07PsPpPaPbPqPoPmPgPYP6PeP6Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0IQ0K'o9^iw/gS%Jl#MQ0H=|6wQ0FQ0GQ0J3^3^/gS=fvF5fvQ0M%F4Q0O7;<%F7Q0P7;<7;1Q0QPMPMPzP{1SQy,<M9UM8P{PMP9P{PM19`y%VDRDQ00#x5r65GMP{PMPLP{PMQ0TP{PMAGMx|P{AGMx}Ar6DE,S},<M5UMCiFkFkF=Q0UQ0Vb;b>b?X46X56X66X76X86Aju<B\hP=PBP4P;C>\3107<?5BN10=;,4<11<;%7;14:G,::[[[[[[^46^56^66^76^86P2P[PXQ01Q0YP0P^PjPdPHPnPrO;b:bQbRbSbTbZbWbIbHbGbFbEbYbVbDbCbPbObNbXbUbMbLbKbJb0-07fEv1L_PRfPFQ0MPtQ0Q%VP9GMxQ0UQ0Vb;b>b?%7PP2b::06_PEvPcAIEfR,cEPTO2ebBbAb[bBbAPj1L]P=IER=RKTRT:05K5,cEB0AK5TO2e1TjTeWaWcP1P2O2n2001000000121000000W0WbP1P2O2n2001000000121000000W0W`P1P2O2n2001000000121000000W0WAWBP1P2O2n2001000000121000000W0W[P1P2O2n2001000000121000000W0Xe6Xf6X_6Wdo"). Qed.

(* [comment removed for export] *)
Lemma app_vs_shadowZ : forall A k S n, ablk A (A + k) -> 2147450880 <= S -> S + n <= 17594333495296 -> A + k <= S \/ S + n <= A.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_kit ()) ["CANSEC1"] "h04__x1h14__x2h24__x3h34__x4h41Ah51Bh61Hh72H1h82H2h91Sh:7__arithh;4__ffh<8__varmaph=5__with>1kh?1np;2p;3p;1p;4p;7p;8g008:j28Tg0142j3YTg009lj13Tg0000j10Tg009Nj1>Tg007^j22Tg014gj4LTg015fj2@Tg00C1j1:Tg00CPj27Tg00]Nj3;Tg00G3j2FTg00G_j1VTg00H?j3ETg00H_j1UTg00I]j2DTg00I?j1RTg00J;j4CTg00JYj1QTg00K7j1NTg00Lgj29Tg00NQj3BTg00Kbj2=Tg00LEj1KTg00OWj2JTg002lj2ITg00P9j2HTg004\j3OTg00Pej3PTg00QDj4GTg00^7j4STg00^bj7TTg016@j7XTg00_jj8WTf0R0#3#3#3#3p=4%00#0p=?%00#0#0#0p=1%30#3p=Mg00`NR1f1R2g00cRP0CSp=5P2g00aSR3g00b2R4P4g00bRR5P0g00c2FTp=6f2R6P3P4P4P5P2P0FXp=Af3R7P3P4P4P5P6P2P0GWp=<p,2rcR31876R87Y7g0056R9#3R:#3#4#4#4R;#3#0#?#1#1#1#>R</26%09R=#0R>#0#?#1#1#4#4#4#4#0#?#1#1#1#>R?,28P3f6R3f5R8,83R@P6CLg016d,2@12?3'@g00f6R@g00fbRA#:RB#:RC#:RD#:,71RE171D171A5;15;1g00gARA'F171C171B5;19;1E/FA%V@5E@3E%U@P1P1f4R@,D1P6%R1CCP21D17CC%Q1%N1RA1919R9191=5B1R=%0;#3#M#1#1#1#>R;,=1'5,6A1=1?RE/59,6A5AA%K4R4PA191:R:191>5B1R>/5E,6AP4PA1=1</5:,6AP415=:,6A15>9,6A5AAC<C<C<1JA5P0P6g00gmRAg00hMR5'I1H06=OA5dg005[=P12CGb;b<b=X01X11X21X311802/2;12?0'@187@R;/2?12<@12;81883/27'@[[[^01^11^21^31P0P8P3f7f8P2P6P7O7b:b5W8W7W6X?1X91X>1X41o"). Qed.

(* [comment removed for export] *)
Lemma zshadow_munch : forall W m m1 X n, zshadow m X n -> munch W m m1 ->
  (forall a, X <= a < X + n -> outside W (shad a)) -> 0 <= X -> X + n <= 2^47 -> zshadow m1 X n.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_kit ()) ["CANSEC1"] "h02Hah14__x1h24__x2h34__x3h44__x4h54__x5h61ah71zh81Hh92H0h:2H1h;2H2h<2H3h=2HOh>2MUh?1Wh@1XhA2X0hB2XNhC2Z0hD7__arithhE4__ffhF6__sat4hG6__sat5hH8__varmaphI5__withJ1mhK2m1hL1nhM1ohN1qhO1rp&0p;1p;3p;2p;4p;6p;7p;8g00H_j1XTg0000j10Tg000Uj1ITg0013j1YTg0069j1yTg006[j3RTg017Xj3kTg007^j2<Tg008:j23Tg00:nj1PTg018Lj2GTg009Nj1CTg009lj1BTg00:Qj2vTg00;fj1TTg004\j38Tg019Bj2qTg00>kj2=Tg00=7j2ETg00=Tj2gTg00>5j1fTg00>Nj2STg00?Kj2cTg008Wj2>Tg00@2j2bTg0093j2QTg00@Yj2aTg00A?j2`Tg00Aej2_Tg00BMj3^Tg00C1j1;Tg00D9j1]Tg00DWj2\Tg00E8j3[Tg00Eak203Tg00CPj2ZTg00FJk302Tg00G3j2OTg00G_k101Tg00H?j3WTg00I]j2NTg00I?k100Tg00J;j4HTg00JYj1xTg00K7j1wTg00Kbj2@Tg00LEj1tTg00Lgj2?Tg00^7j4FTg00MJj6pTg00Mnj3oTg00NQj3KTg00O4j3lTg00OWj2nTg002lj2jTg00P9j2iTg00Pej3rTg00QDj4hTg00R6j1sTg00Roj6MTg019hj3uTg003Fj2UTg00nMj2VTg01:Kj2eTg00<Uj2zTg00\Rj6{Tg00]Nj3dTg00^bj7|Tg00_Fj7}Tg00_jj8~Tf0R0#0#0p=Jf2R1f1R2/>0'Qp=4g005[R3/<0p=2%B0#Bp=5%00#0#0#0#0#0#0#0p=6g00`NR4/Z0p=9Ad420p=7P4P2g00`lP0CFp=DP2g00aSR5g00b2R6P6g00bRR7P0g00c2F|p=1P4P2g00cRP0CFp=AP1P5P6P6P7P2P0F}p=Lf3R8P5P6P6P7P1P2P0G~p=:%00#0#0#0p=mg01;:#Xg0056R9#0R:#0R;#0R<#0#JR=#IR>#Y%I<R?#YR@#yRA[RBAR820f5RCf4RD;k81<D013D8740f8RE%P2RF'G[^64%2D13CD%C:RG%B:RH#B#5RI#CRJ'vRK'<f7RL/<0f6RM,3L740PAf:RN%TFROO1PN%P1#TO1=8A0XMAPCPOP41q>FRAf<RP/G0X74RQP4PFPQPDP2P0O2%J=#6#6#6#6#6#6#6#CR=,=FP4g00d`%C<R<,E2'3RQ%20?40=X741g2<A84<3RR#f1E1<,S<1=1<'39841[1c1<1>3<RS1=8<RT#2?4T<[1b8<1><31=D<RT,><1<T3'Q[1aD<1EC<=843\R1`C<1=M<=84M\R1EM<P41=L<P41_GJ1>3G%2J1>3K[[%2GRTg00eZRUA^GJ2UW0%2K\U^0Tg00f6RTg00fbRU#;RJ#;RV#;RW#;RX#;RY#;RZ#;#9%]9,\4%9YRY5[4%9W%9V2034<1Z4U6024RU'7'7'7'7g00gARV'O%9Z%9X%9J/7U'7,7Y'7/OV&01T5WT3W%XTP4P41N4DP1&004RTCHP2P41N4CP8PTCHCH%x4%w4RTPT1@43RV1@4<RY'D,1T%t6RU1?4HRH,AV,1T1DHY,1T5LTC:PUPTPTPTP5P6P6P7P4PYg00d9R6PVCF,1TEpPUP41?4;R;P61?49R69o4Y=K4HCF,1TC:PUPT1?4:R:/A;,1T%B9R9,?49K4:RH,D;,1T5LTPUPT1@4G%II5l4,AH,1TPUPT1AV:,1TPU%59#5#5#5#5#5#5#0#J#m#6#CR9,@4=K46R6,AV,1T1@4=,D6,1T5LTC:C:C:C:C:1nT7P0P1g00gmRTg00hMR7'j1i01=8T7dAr432ChbEbHbIX14X24X34X44X54%2CR7?4C<\Sg00hm\R1S<1/3M984C[1<8C138D74C13DC/<K139CR9#2?49=\7[[[[^14^24^34^44^54P0P8f;R8fAfBPDPEf9PNPPf=O:bDbFbGbObNb<b;b:b9b8%2Q?4Q=ePF%s2EM9uF=EM1G8Ae1U>F,V>1e>FEM1V>O,G8eO21U?3,z@PMP2P0O2E{W0X64ARLMCeWBWAW=W>WCXL4X@4XKBWJW?o"). Qed.

(* [comment removed for export] *)
Lemma shad_outside2 : forall X n A1 k1 A2 k2, ablk A1 (A1 + k1) -> ablk A2 (A2 + k2) -> 0 <= X -> X + n <= 2^47 ->
  forall a, X <= a < X + n -> outside [(A1, A1 + k1); (A2, A2 + k2)] (shad a).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_kit ()) ["CANSEC1"] "h04__x1h14__x2h27__arithh32D2h44__p1h54__x3h62Hah74__ffh88__varmaph95__with:1oh;2D1h<4__x4h=4__x5h>2A1h?2A2h@1HhA2H0hB2H1hC2H2hD2H3hE2H4hF2H5hG2SRhH1XhI2X0hJ2XNhK6__sat6hL6__sat7hM1ahN2k1hO2k2hP1nhQ1qhR1rhS1zp&0p;2p;3p;1p;4p;6p;7p;8g008:j20Tg0142j3`Tg0000j14Tg009Nj1ATg009lj17Tg00:Qj2nTg008Wj22Tg00=7j2MTg00=Tj2zTg004\j3GTg00>5j1STg00>Nj2^Tg00>kj2JTg00?Kj2tTg0093j2CTg00@2j2mTg007^j21Tg00@Yj2jTg00A?j2iTg00Aej2gTg00BMj3fTg00C1j1>Tg00D9j1eTg00DWj2dTg00E8j3cTg00Eaj2bTg00CPj2WTg00FJj3aTg00G3j2VTg00G_j1UTg00H?j3;Tg00H_k105Tg00I]j2PTg00I?k104Tg00J;j4LTg00JYk103Tg00K7k102Tg00Kbj2DTg00LEj1yTg00Lgj2KTg00^7j4NTg00Mnj3xTg000Uj1wTg00O4j3vTg00OWj2uTg002lj2sTg00P9j2rTg00Pej3qTg00QDj4pTg00:nj18Tg00R6j1oTg00Roj6lTg00SMj3XTg00Shj3ZTg01;lj7YTg015fR0j2[Tg01=4j2kTg018Lj2RTg01=Tj4HTg00]Nj3hTg00^bj7_Tg00_Fj7{Tg00_jj8|Tg00MJj6}Tg00NQj3~Tg011Vk400Tg0126k601Tg005[R1f0R2'1p=E%72#7p=\f2R3f1R4'0/12p=31134/C2p=6%72#7#7#7p==%42#4p=T%42#4#4#4p=<g00`NR5/W2p=?Ah542p=:P5P4g00`lP2CNp=OP4g00aSR6g00b2R7P7g00bRR8P2g00c2R9F_p=FP3P6P7P7P8P5P4g00cRP2CNP9F_p=5P3P6P7P7P8P4P2F{p=If3R9P6P7P7P8P3P4P2G|p=9P4P6P7P7P8P2E}p=QA~542p=@P5P5P4P2H00p=BP4P6P7P7P8P2J01p=]p,2rcR610937`910349`63f7R6#Ef8R:g0056R;#4R<#AR=%7<R>#7#\R?#AR@'nRA736f:RBf9RC,0BRD,22762P5g00d`%4<RE#4RF#ARG,M4'0RH%7;RI#\#=#=#=#4#T#<#<#<#ARJ%A;RK%TF#<#<#=#=#=#=#4#T#<#<#<#ARF532762XS51z4GAG5G1RL#S1M3G,^G1J3G'09G53[1t3G121GRM1J9GRN#E12NG'C[1m9G12G1f4RN/JGRO,2G11O1'C[1jNGf5RO/MG=G51\L1iOGf6RP/JG=G5P\L1MPGP51J6GP51g=@121=%E@121A[[%E=RQg00eZRRAf=@4UW6%EA\R^6Qg00f6RQg00fbR@#>RS#>RT#>RU#>RV#>RW#>RX#>#?%e;,d5%?WRW5c5%?U%?T1b5G1W5@5a5R@':':':':g00gART'V%?X%?V%?S/:@':,:W':/VT%UQRT5;Q3;&05QRQP5P51P5NP3&045RWCLP4P51P5OP9PWCLCL&035R@&025RSPS1D51RV1D5GRX'O,FS%y7R71K5>R>95SV1O>X,FS5ISC9P7PSPSP5PXg00d9RUPVCN,FS,QSP7P51K5EREPU1K5;R;9x5X/@>CN,FSC9P7PS1K5<R<=5SE1K5IRI,@<R>,OE,FS5ISP7PS1D5=%w?5v595S>P7PSA5SV<P71D5JRV1@V;RV55S1D5KR>,@V1D5F55S5ISC9C9C9C9C91uS8R8P2P3g00gmRVg00hMR?'s1r23=GV?dAq514CpR1b7b8b9X05X15X55X<5X=5%EOR?12OG'C\Mg00hmRM\L1^G3/0P9G5O[109N,2O969OA3NOA10JORAA3AKF56J\?[[[[^05^15^55^<5^=5P2P9f;R?fDfEPNP:PCPBf<RAf=RGO:b2bKbLbRbQbFbEbDbAb@A3HKF96JHe%84RH%o4ElA3HKF96JHPBPC%83RHPKPP11JHRL10HKRV/1FR=;X2AZL=2FY11DH11VB'[P010?BRV%89RH'1A3HK?1k55RH10A?R=,BA1BBD%UHRD5;H3;%8NRL'RP211=LP?PB%8ORBPKP:11JBRJ10BKRE/1FRF;X9AZJF9FYRF11VB11E?'[REP0%8PRP,1=R=A3PKARPf?R?f>RB,0?RV'B10GARJ,BG=;HD5;H%86R6'RRXP211J6RJf@RU%8:R:10U?RY,2:36#SRZ10BGR[,2:96B:#SR\/CRR]p-0R^PTPQP51P53R_P41P59CLP@PS1@;IRI=5S<P71]SO1O<I,FS5IS,QSC9P8P1b7b8b9X05X15X55W4RIA32341049,23,CNPM[[^05^15^55^4^ROP2fAR`%8CRC'1PUPCP`PNO5b2RaP\PRPIPOP211?CPBPCP?P4O5b2g01=oROCHRICH1BUY1BB[=;HD5;H/R:R:eW3P2O1A36KGR6PZP]PaP\PRPTPQP5P_P4PWCLP@PS1@<>=5S;P7A5S;<1]SN5IS,QSC9P8P1b7b8b9X05X15X4^R1A34K2A6439PM[[^05^15^4^R^P212CVPCP?P4O4b2POCHROCHP:eW3P2O1n200100000021100011000b:W;P2O1A3LKAPFPEP0P=PPPXP2PZP]P1P^P210`U,2CPCP`PNO4b2RNPICHP:eX3JP2O1PZP]PNPOCHP:eX36P2O1n200100000021100011000b:W;P2O1n200100000021100011000b:bGW6XM5WJWIWCWBXO5X?5XN5X>5XP5XH5o"). Qed.

Lemma shad_outside1 : forall X n A1 k1, ablk A1 (A1 + k1) -> 0 <= X -> X + n <= 2^47 ->
  forall a, X <= a < X + n -> outside [(A1, A1 + k1)] (shad a).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_kit ()) ["CANSEC1"] "h04__x1h14__x2h24__p1h34__x3h42Hah57__arithh64__ffh78__varmaph85__with92D1h:4__x4h;4__x5h<2A1h=1Hh>2H0h?2H1h@2H2hA2H3hB2H4hC2SRhD1XhE2X0hF2XNhG6__sat5hH6__sat6hI1ahJ2k1hK1nhL1ohM1qhN1rhO1zp&0p;2p;3p;1p;4p;6p;7p;8g008:j20Tg0142k304Tg0000j13Tg009Nj1CTg009lj16Tg00:Qj2iTg008Wj21Tg00=7j2JTg00=Tj2yTg004\j3ATg00>5j1XTg00>Nj2VTg00>kj2GTg00?Kj2oTg0093j2FTg00@2j2hTg007^j24Tg00@Yj2eTg00A?j2dTg00Aej2bTg00BMj3aTg00C1j1;Tg00D9j1`Tg00DWj2_Tg00E8j3^Tg00Eaj2]Tg00CPj2RTg00FJj3\Tg00G3j2QTg00G_j1TTg00H?j3MTg00H_k103Tg00I]j2NTg00I?k102Tg00J;j4ITg00JYk101Tg00K7k100Tg00Kbj2DTg00LEj1xTg00Lgj2HTg00^7j4LTg00Mnj3wTg000Uj1vTg00O4j3uTg00OWj2tTg002lj2nTg00P9j2lTg00Pej3kTg00QDj4jTg00:nj1@Tg00R6j1mTg00Roj6gTg00SMj3pTg00Shj3qTg01;lj7fTg015fR0j2rTg01=4j2sTg011Vj4WTg018Lj2STg01=Tj4YTg00]Nj3cTg00^bj7[Tg00_Fj7zTg00_jj8{Tg00MJj6|Tg00NQj3}Tg0126j6~Tg005[R1f0R2'4p=B%62#6p=Uf2R3f1R4'0/42p=21434/F2p=9%62#6#6#6p==%32#3p=P%32#3#3#3p=8g00`NR5/R2p=<Ac542p=:P5P4g00`lP2CLp=KP4g00aSR6g00b2R7P7g00bRR8P2g00c2R9F[p=>P3P6P7P7P8P5P4g00cRP2CLP9F[p=5P3P6P7P7P8P4P2Fzp=Ef3R9P6P7P7P8P3P4P2G{p=7P4P6P7P7P8P2E|p=OA}542p=?P4P6P7P7P8P2E~p=Zp,2rc10428044f4R6#Bf5R:g0056R;#3R<#CR=%6<R>#6#UR?#CR@'iRA726f7RBf6RC,0BRD,12792P5g00d`%3<RE#3RF#CRG,J4'0RH%6;RI#U#=#=#=#3#P#8#8#8#CRJ%C;RK%PF#8#8#=#=#=#=#3#P#8#8#8#CRF522792XO51y4GAA5G1RL#X1J3G,VG1G3G'09A53[1o3G111GRM1G9GRN#B11NG'F[1h9G11G11G6GRN,1G14N1'F[1e6G1J:G=A51\L1d:G1GCG=A5C\L1JCGP51GBGP51b=@111=%B@111A[[%B=RNg00eZROAa=@4UW4%BA\O^4Ng00f6RNg00fbR@#;RP#;RQ#;RR#;RS#;RT#;RU#;#<%`;,_5%<TRT5^5%<R%<Q1]5G1R5@5\5R@':':':':g00gARQ'Q%<U%<S%<P/:@':,:T':/QQ%TNRQ5MN3M&03NRNP5P51N56P3&025RTCIP4P51N5:P9PTCICI&015R@&005RPPP1D51RS1D5GRU'K,>P%x7R71H5>R>95PS1K>U,>P5EPC7P7PPPPP5PUg00d9RRPSCL,>P,OPP7P51H5EREPR1H5;R;9w5U/?>CL,>PC7P7PP1H5<R<=5PE1H5IRI,?<R>,KE,>P5EPP7PP1D5=%v?5u595P>P7PPA5PS<P71D5JRS1?S;RS55P1D5KR>,?S1D5F55P5EPC7C7C7C7C71tP8R8P2P3g00gmRSg00hMR?'n1l23=AS?dAk514CjR1b6b7b8X05X15X35X:5X;5%B:R?11:G'F\Mg00hmRM\L1VG3/0C9A5:[1096,1:999:A26:A10J:RAA2AKF59J\?[[[[^05^15^35^:5^;5P2P9f;R?fAfBP6f8RAf9RGf:RLf<f=O:b5bGbHbNbMbBbAb@b>b=A2HKF99JHe%@4RH%m4EgA2HKF99JHPBPC%@3RHPKP:14JHRJ10HKRS/4FRF;p2AqJF2Ff14DH14SB'rP0%@9R092ABA20KA1s55R0P5P5PG10GARACW%T0RB3M%@6RS'SP214AS%@:RA10LGRH,1A59L#XRDPOp-0RFPQPNP51N53RJP41N59CIP@PP1?;IRI=5P<P71ZP:1K<I,>P5EP,OPC7P8P1b6b7b8X05X15X35W2A22341049,13,F6PM[[^05^15^35^2FP2%@CRC,4?PLPCP?P4O5b5g01=oRICYP5P5PLPHCW=M0B/SARAeW9P2O1A2SKGPDPOPQPNP5PJP4PTCIP@PP1?<>=5P;P7A5P;<1ZP65EP,OPC7P8P1b6b7b8X05X15X2FA24K2A9439PM[[^05^15^2FP210?L,1CPCP?P4O4b5PICYPAeW9P2O1n200100000021000010000bLbCW4XI5WFWEW?XJ5X<5XK5XD5o"). Qed.

(* [comment removed for export] *)
Lemma lowprob_lenA : forall nc tl f s syms snext hT fm r,
  lowprob_loop nc tl f s syms snext hT fm = Ok r -> 0 <= s -> (0 < f)%nat -> s + Z.of_nat f <= Z.of_nat (length nc).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_kit ()) ["CANSEC1"] "p'0h02RLh15syms'h27__arithh34__x1h44cstrh53Hf0h64__p1h75cstr0h82fmh92hTh:1rh;1sh<5snexth=4symsh>2Hfh?4__ffh@8__varmaphA5__withB2IHhC4__p2hD4__x2hE1ahF1fhG1xi001xhH1HhI2HshJ2LDhK3RL0hL4__x3hM1chN2_HhO1bi011bhP1mhQ1ni021nhR2nchS2syhT2tlhU1yp%0p&0p;1p;2p;8p;3p;4p;6p;<p;7p;Bg00H_j1aTg0069k10=Tg01=4j2\Tg01>Kj1[Tg01?Dj87Tg01@Lj2QTg004\j36Tg00XcR0j13Tg008:R1j20Tg007^R2j2<Tg01AER3j2oTg008WR4j2OTg002lj2bTg01A]j4ITg01BDj1ATg00G_j1hTg00I?k104Tg00JYk103Tg00K7j1}Tg00Kbj2eTg00LEj1xTg00OWj2tTg00P9j2sTg00Pej3rTg00QDj4qTg00C1R5j12Tg01Bij2NTg00D9j1pTg01Caj2FTg009Nj1cTg01D>j24Tg0000k10;Tg01D[j6kTg0093R6j2>Tg01EbR7j2jTg01F<k408Tg01G?j2ZTg00I]j2`Tg00J;j4iTg00Lgj2_Tg00NQj3PTg01H7j3HTg01I9j4gTg01J1j4WTg01J\j1|Tg01K:j4{Tg009lj1zTg01K]j4yTg01L>j2dTg01L^l<^Tg00^7j4mTg00^bj7~Tg0126k600Tg00_jj8wTg00H?j3lTg01MCk301Tg01M`j1fTg01NWj1vTg00:Qj2uTg01OVk105Tg01PRk206Tg00_Fk707Tg01Pol<nTg01QTmB0:Tg005[R8f0R9'<p=9g00fbR:/o9p==g00`NR;/d9p=Kg012ZR<P;P3P0P4g01R:R=P:P8f1R>P:P8P9M<^p>09P;P>g00`lP9Cmp=]P>g00aSR?g00b2R@P@g00bRRAP9g00c2F~p=EP>P?P@P@PAP9J00p=Xf3RBP?P@P@PAf2RCP>P9Gwp=R1d;9#3p=;10C>/<9p=JAl;>9p>0<B01;>9p=1f7RDf6REf5RFf4RGPBPC%f>P9G7p=:PFPGAHBC>P9Cgp=B%v>=l;9p=D1uC>$050069p=@1Q>996BCp=5%3>,0C/<9p=CA6;>9p=MPCP?P@P@PAP>P9K07p=YP;P>g00cRP9Cmp=S14>9#fp>021O89p=G1b;9p=8P<P<P;P;P5P0P0PBg01R\PCP>P9M<np=?P<P;P3P0P4P=P:P8PBPCP>P9M<^p=LP<P;P;P;P0P0PFPGPBPCP>P9M<np=TP;P;P;P;P;P;P1P9P>PCP1PBPGPFPEPDf8R1f9R0NB0:p=VP;P;P2PDP2PEPFPGPBPCP>P9M<^p=U%a;R2&0=;#aR=1\=2/\;/\;R4%[4R3P0P1PEPFPGPBPCP>G71Q49R536%9ER?%=1RH%30RI,01RJf<RK#KRL#3RM'<[[[]:^8;^9;^<2]=^;;S00XF<P1PDP:PFPGPBPCP>G7=6351o::RNPN1O88RO1b;8RP009PP9CIPO%AL%9Mp-0RMg00f6RL#hRQ%aLRL&04;RR&03;RS%};RT1e;8RU/]U,ET%x@R@1XTCCR1tTARAP9PCg00gmRVg00hMRW'b1s9C=6VWdAr;8>CqRWb?b@bAW6P>\O^6MP9f;ROf>RX#;7J8PCO2b2b4b5W>XI?W0X:4X8;X9;X<2X==X;;Q00f:RYP0%2DRZPFPGPBPCP>G7=635%20R[#=P;P4f=R\/N1PVP3g0056R]#pR^,F9R_P=P4P1PEP0f?R`PXPK%c]Ra,0YRbP9%h;Rc-0<aRd,1114DaPEG:X1=EBPXP\PO100aP11D9cRe,1DPEPVP;&0;]Rf#cRg14\a;@9P8PFn0100000020000G7n0100000020000RhXM;PBPCEk%[;Ri1NX01Q;9Rj36P3PhP4PGC5'>XE;,j;P7P;1N`Y=6ijP3PVP3P_P=P4P0PDPYf@RhP`P\10OaP9110d141aPDG:X1=EBP`PXPKPbP0111ePDPVP;14XaRb=@g9P8PEn0100000020000G7n0100000020000P4PFC5'>XE;%2K%;`5CYP9fARk/NK=6ijP3PVP3P_P=P4POP0PKfBR_PkP`10\aRjP911Od14YaP0G:X1=EBPkPhPX10KaPO11YeP0PVP;14ha=@g9P8P1n0100000020000G7n0100000020000P4PDC5'>P6Pi1N_\P;P>C5P3PVP31F>^P=P4PKPYP\fCReP_Ph10XaP911Kd14OaPYG:X1=EBP_PkP`PjPK1D>c,1OPYPVP;14kaRj=@g>P8P0n0100000020000G7n0100000020000P4P1C5%2hS01#3Rl%;e5JXP9PifDRi/N`P;PBC5P3PVP31FG^P=P4P`P\PhfFRmfERnPe10kaP911`dPbP\G:X1=EBPnPiP_10haP`1DGc,1XP\PVP;14ia=@gGP8PKn0100000020000G7n0100000020000P4POC5PmPkPFP>H08%9k%;m,Ok'>1Zkm,MF'>P<fNRbfMRoPEPFPGPBPCP>G7=635fQRp#KS02#3S03,<J\H\?[^:4^8;^9;^<2^==^;;P3PVP31F1^P=P4PePkPifJRHfIRJPC10naRqP911ed14_aPkG:X1=EBPJfHRrP>10iaRsPe1D1c,1_PkPVP;14raS04=@g1P8Phn0100000020000G7n0100000020000P4P`C5%2CRt#=%2BfKRu#;5Cm]>]0]BPiPofLRvP:PFPGPBPCP>G7=635fPRw#;Rx9C1:\N\?[^:4^8;^9;^<2^==^;;P3PVP31FD^P=P4P_PhPePJPrP:PsP911_dPjPhG:X1=EBPrfGRjP:10eaP_1DDc,1kPhPVP;14jaRs=@gDP8P`n0100000020000G7n0100000020000P4PXC5%2:#=%KHR:#A%3:#9PQPLP;1`;CS05P>PRCiPSPT1XTGRR1_;]R:1_;fRf'],ET5YT1XTF5YTP@1e;aRN9P;:Ry/Sf,ETCRPAPWb?b@bAX3;XD;X6MXCM1O9>,>C/>B10>aRz/<C[^3;^D;^6M^CMP91Zjv,MO%9j%;vPjPFO5b2b4W>W0WBfOR{Pb%2ER|PFPGPBPCP>G7=635%21#=fRR5#;S069C1[[\?[^:4^8;^9;^<2^==^;;P3PVP31F0^P=P4PiP_PnPuPHPt10maP911id14eaP_G:X1=EBPHPJ%2>PqPi1D0c,1eP_PVP;14Ja=@g0P8Pkn0100000020000G7n0100000020000P4PhC5%2t#=1FO^PVPVP3PVP3P9P=P4AHrmJR^P{PbP|10HaP911rdPsPmG:S07X1=RsCgPbPo%2FRt10JaRqPr1D\c,1jS08PmPVP;14oa=@g\P8Pnn0100000020000S09G7n0100000020000P4PiC5%2|R1#3S0:,0HS0;%K{S0<#3R}'<S0=]0P9P=P4PjPnPrPbPoPtPqP911jd14maPnG:X1=EB1Q4eR~563P=P4P^PsPiP9Ek%[=RsAHJjH1Q=9R^36P3Q07P4PnC5'>XE=,j=P7P=AHHru=6s^P3PwP{PZ10uaR7P911JdQ04PjG:P4PmC5'>XE=%2Z=CuxP9AHvHo=6s^P3P5PpP[10oaP911ud14HaPJG:P4PrC5'>P6PsAHoubP=P>C5P3fSR6P5%2Y10baP>11vd14uaPHG:P4PJC5%2O#2fTRJ#;S045C{P9PsAH{owP=PBC5P3fVRsfU%2\10paPG11{d14baPoG:P4PvC5P\105aR\PF11wd202{aPbPoP9%2XRw#2Rd#=%3XRp/0aRu/0a#GR[PPPd109aRdXG;R^P^PpO1S07O1P^PwQ07P^PXPp%8pC?S07C?CLPOCIS0>P[fXS0?#KRp#AS0@%3pRp#9S0A%AhS0B%3hRX#9S0CPQPL1`;>S0DPSPT1SU:,ETS0E1XTB5YT=YTRP@1SUy,ETCRPAPWb?b@bAX3;X6MXCMS0F%99RR/>>/>C%9z[^3;^6M^CMS0GP9f[RM,Zs,MH%;M,OsPsPiO4b2b7b4b5%=w%GuPPPwPuQ07CLQ0>P[Q0@Q0AQ0BQ0CPQPLQ0DPSPTQ0EP@1]Uy,ETCRPAPWb?b@bAX3;S0E%Gz\R^3;S0DP9%3_RRP>O2b2b7b4b5CWO9fW#;9C\w%2`Rw#2R\#3S0C,06S0B/<p%3`RU/0aS0A/0aR[,06Ru/<pP9XG;Rs1<>9#|XU;XG;RMQ0BPuPsPsPsP;P;g01S@10>9C{#8XP;XQ;RuP6P6%86Q0CP[PsPs%39#8XG<R6P\P[P^PwQ0AP^P`PU%8UC?R`C?ETM:VPpPp%8pGU%=\%G[R[PPP\P^P^PUO1RUO1P^PwPUP`C?CLPKCIP[10JaRJ/0lR[fY#;R`'<10Xa=JJ`RUPsPMP[PsP^PXO1R[O1Rw,0JPsPsPsPuPJPJ%8JPlPwPsPsP6Q01P[P^PhPX%8XC?ETM:VP`PsP`O1RX%8X1M`XeGUP>CIPUfZ#KRU#A%3U#9%A_%9RPQPLP;Q05P>1`;BCiPSPTAP;fNRf9P;y%z],_;R]'S,ETP@AP;fN9P;:/S],ETCRPAPWb?b@bAX3;XD;XL;RWAJdzC10Ca/0a=J>B[^3;^D;^L;RdP9f]#;%3iQ0?PBO4b2b7b4bKb5CWb0W0WNP>P9O2n2001000000121000000WHXS=P>P9O2n2001000000121100000b0W0PoPv%2G10raPj1DKc,1mPnPVP;14va=@gKP8Pin0100000020000G7=63~PGPqPrQ08PmQ09PiP9%2tRi#=%3FRm/0aRr/0a#GRGPPPiP^P^PmO1RiO1P^PtPiP^PFPm%8mC?RmC?CLPCCIRFPGQ0<#ARi%9}R~%ADR3%3DR8#9RgQ0FQ0GP91Zo5,MkQ06,OoPoPOO4b2b7b4b5%=t%GrPPPtPrPmCLPFPGPiP~P3PgQ0EQ0DP9PIP>O2b2b7b4b5CWO9%;b9CqtQ0=%3ERq/0aRt/0aRb,0HRg/<}PsPMQ0;PgPsPsPsPuPHPH%8HQ0:PbPsPsP6P1PbP^P|PtP^PEPq%8qC?REC?ETM:VP}P}%8}GU%=1%GbRbPPP1P^P^PqO1RqO1P^P|PqPEC?CLPBCIPb%3ZRb,07RE/<x108a=J7xRaPsPMPEPsP^P8O1REO1RM,07PsPsPsPuP7P7%87PbPMPsPsP6PZPEP^PDP8%88C?ETM:VPxPsPxO1Rs%8s1MxseGUP>CIPaQ02#AQ03#9%A0%9IPWPdP9Q04%3OP{PBO4b2b7b4bKb5CWb0W0n0110100020101PCO1bOW>W0WBXF<P9O1n0110201020111102PeP>PYO3bJW0WJP>P9O2n2001000000121000000WHXM;P>P9O2n2001000000121100000b0W>XI?W0X:4X8;X9;X<2X==X;;WBXF<P9CyXF<XT;WRo"). Qed.

Lemma tsym_nilA : forall syms, tsym [] syms = [].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_kit ()) ["CANSEC1"] "p'0h01oi001oh14symsh25syms0i011lp;1p;2p;3g0069j18Tg00H_R0j11Tg0000j10Tg000Uj12Tg0013j17Tg00G_j16Tg01Sdj24Tg004\j33Tg002lj25Tg00`N#8R1#1R2P0P1g0056#0#0#0#2#7R0#1R3%60R0f0R4'4;30P41530R0P0X12X01f1P4O2n10110100020020100101W2o"). Qed.

(* [comment removed for export] *)
Definition wkb (jw : list byte) (snext : list Z) : list byte := u16s (map (Z_to_bv 64) snext) ++ skipn (2 * length snext) jw.

Lemma wkb_length : forall jw snext, (2 * length snext <= length jw)%nat -> length (wkb jw snext) = length jw.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_kit ()) ["CANSEC1"] "h01nh14__p1h24__x1h34__x2h44__x3h51Hh62H0h72H1h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>2jwh?1mh@5snexthA1xhB1yhC2z1p&0p;1p;2p;4p;3p;<p;6p;7p;Bp;8g0000j19Tg000Uj1YTg0013j1UTg00H_j1GTg00C1j1ITg01Tdj26Tg01L>j20Tg01U;R0j2XTg003Fj1`Tg01UUj4LTg01V1j1[Tg01Vlj3JTg01WJj2;Tg01Waj2MTg009Nj1yTg00XcR1j11Tg00>NR2j24Tg01D>j27Tg01X8j2=Tg008:R3j2STg004\j32j1VTg01XUj2eTg01Y8j3dTg002lj2ATg01L^l<NTg007^R4j28Tg01A]j4\Tg01BDj1KTg01YUj2ZTg008Wj2QTg0093j2>Tg015fj2RTg00CPj2?Tg00]Nj3@Tg00G3j2HTg00D9k101Tg00DWk200Tg00E8j3~Tg00G_j1}Tg00H?j3CTg00I]j2WTg00J;j4{Tg00JYj1xTg00K7j1wTg0126j6rTg00Lgj2DTg009lj1qTg00Kbj2TTg00Mnj3pTg01Z7j3oTg00^7j4FTg016@j7mTg00LEj1lTg00NQj3kTg00OWj2jTg00P9j2nTg00Pej3iTg00QDj4hTg01J1j4gTg01ZZj4fTg00Roj6<Tg01[9j3sTg01[Zj1tTg01MCj3uTg01\\j3vTg01];j2cTg01QTlBBTg00^bj7zTg00_Fj7bTg00_jj8|Tg00`NR5f0R6'0p=5g012ZR7f1R8;26p=3P7P7P7P5P5P5g01^8P1P1P1P2g01^Xf5R2f4R9f3R:f2R;P8P6MBBp=aP7P7P7P5P5P5g01_;P1P1P1f6R<g01_[P2P9P:P;P8P6MBBp=_P7P7P7P5P5P5g01`BP1P1P1P3g01`bP2P9P:P;P8P6MBBp=^P7P5P0P1P4g01aEP2P9P:P;P8P6M<Np=]P5P8g00d9P6CFp=EP8g00aSR4g00b2R0P0g00bRR3P6g00c2Fzp=:P;P4P0P0P3P8P6Fbp=PP:P4P0P0P3P;P8P6G|p=Og0056R=#9R>#9#9R?#Y#UR@#G%G5g00fbRA#IRB#IRC%56'610@8'XP7P5%9?#9#9#YR?#URD%`?R?P8CLRE#[RF,0@RG%58RH,6CRI=J@;RJ,0@RK';10@:RL,36X07P710DERM,6C%5;RN,6CRO=J@:,0@,;6/3LX07P710@;RP/MIRQP5PDP?P;CL,0D,6C/;6/3LX07P7PH16C61MLO';/3LX071;IQRL/3P%y>RO%1HRR'4RSg005[RT%1PRU/7S'=RV'SRW=25UP7P5%V7P1%V5%18%1652513861e863dXB7XA7PLPWPIPSPCPO1A5OPHPR1A5REaRRPQPV1786,=TX?5X05PPPU1A5URVPIPSPRF_E^PPPUPVM<N1XIP18SURQPIPSPRPPPUPVE]P6C\PQ%KN%1N,8T10@9RN#K%1N,8T10@2#1%59#1,4O'7RN,ZT1QTN1=TNRQ=25N'>18NTA25QT'>'R10@<#1%52#1,4O'7,=TP5p-0R<g00f6RQ1?5CRN1?5B1?5ARA5@55@5g00gARB'H%IC,?5&01=-005=~5N=@5ARA5@5/HB1HAB%}Q5CQ5CQ3C%GQP51W5;P81W5:C{%x5%w5RQPQP4P0P0P3PQP4P0P0P3P2Er1D5>R>%q=,D5R41T5O1D5=5p5R=5o5RA'E,:Q5PQP5PAg00cRRA1T5TRBCF,:Q1E>B,:Q5PQFm%l0R0PQP5P=PAP4CF,:QP0Ak5=>/E4,:QCOCO1jQ3P6P;g00gmRQg00hMR3'A1n6;=2Q3dAi5T8Chb9b:b;X25X35X45W114O6,7;R39258,>:183TA258T'>'R14O8/8:14O;/S:=259[[^25^35^45^1<P6f8,0@#1R6f7#5#1R<,4O'7,QTP6P8P<P;P2O6b8bCb7b=b<b6CgPMP5PDP?P8CfE<PKAs@I;E<PG%tEE<Au@FJ,0@Av@FJE<1c;8,0@/3PeW5W@W>o"). Qed.

Lemma wkb_snoc : forall snext jw v, (2 * length snext + 2 <= length jw)%nat ->
  upd_bytes (wkb jw snext) (2 * length snext) (le2 (Z_to_bv 64 v)) = wkb jw (snext ++ [v]).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_bdt_kit ()) ["CANSEC1"] "h01Hh12jwh25snexth31vp;1p;2p;4p;3g00H_j15Tg0000j10Tg000Uj12Tg0013j17Tg00C1j16Tg01L>j21Tg01Tdj23Tg01WJj2<Tg01U;j2;Tg01agj4:Tg01];j24Tg003Fj28Tg01bjj19Tg01cZj3ATg00G_j1@Tg00H?j3?Tg01MCj3=Tg004\j3>Tg00`NR0#5g0056#0#0#0R1#2#7R2#5R3g00fb#6#6R4f2R5,10'3/<4f1R6,12';f3R2P5P6f0C:14521102,34%01#0#0#2/86#93A%@09?069=02,455>3eW0X30W1W2o"). Qed.

End CANSEC1.

(* [comment removed for export] *)
Notation srai48_short := RF_huf_bdt_lp.srai48_short.
Notation land_neg_b2z := RF_huf_bdt_lp.land_neg_b2z.
Notation snext_snoc := RF_huf_bdt_lp.snext_snoc.
Notation le2_mod16 := RF_huf_bdt_lp.le2_mod16.
Notation shl32_shr30 := RF_huf_bdt_lp.shl32_shr30.
Notation swrap32_u32 := RF_huf_bdt_lp.swrap32_u32.
Notation zx16_lit := RF_huf_tbl_kit.zx16_lit.

(* [comment removed for export] *)
Ltac brute_regZ n r lo cnt g :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      let F := eval pattern r in e in
      lazymatch F with
      | ?f r =>
          let H := fresh "BR" in
          assert (H : forall r0, lo <= r0 < lo + cnt -> (f r0 =? g r0) = true)
            by (apply (brute_range (fun r0 => f r0 =? g r0) lo cnt); vm_compute; reflexivity);
          replace e with (g r) by (symmetry; apply Z.eqb_eq; apply H; lia);
          clear H
      end
  | _ => fail "brute_regZ: register" n "holds" w
  end.

(* [comment removed for export] *)
Ltac bdtA_acc_hint :=
  lazymatch goal with
  | |- acc_in ?R (Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880), 1%nat) =>
      let X := leftmost a in
      match goal with
      | H : rng R (shad ?A) (nshad (?len + ?A' mod 8)) |- _ => constr_eq X A; constr_eq A A'; apply (acc_shZ R A len a H); lia
      end
  end.

Ltac wk_mods := repeat match goal with |- context [?x mod ?m] => rewrite (Z.mod_small x m) by lia end.
Ltac wk_land64 := repeat match goal with |- context [Z.land ?x 18446744073709551615] =>
  change (Z.land x 18446744073709551615) with (Z.land x (Z.ones 64)); rewrite (Z.land_ones x 64) by lia end.
Ltac wk_zbnd := wk_land64; rewrite ?Z.shiftl_mul_pow2 by lia;
  (try change (2^1) with 2); (try change (2^2) with 4); (try change (2^3) with 8); wk_mods; lia.

Ltac wk_shz r :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  let v := reg_val r in
  lazymatch v with Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880) =>
    match goal with ZS : zshadow mm ?X ?n |- _ =>
      let RDB := fresh "RDB" in
      pose proof (chkZ mm X n a ZS ltac:(wk_zbnd) ltac:(wk_zbnd)) as RDB; zstep; rewrite ?sxb0; clear RDB end
  end end.

Ltac wk_src r := let v := reg_val r in
  lazymatch v with
  | Z_to_bv 64 (?A + ?i) =>
      match goal with H : bytes_at _ _ A (map (Z_to_bv 8) _) |- _ =>
        let RD := fresh "RD" in pose proof (HufWalkKit.src_rd _ _ _ _ i H ltac:(lia)) as RD; zstep; clear RD end
  | Z_to_bv 64 ?A =>
      match goal with H : bytes_at _ _ A (map (Z_to_bv 8) _) |- _ =>
        let RD := fresh "RD" in pose proof (HufWalkKit.src_rd _ _ _ _ 0 H ltac:(lia)) as RD; rewrite Z.add_0_r in RD; zstep; clear RD end
  end.

Ltac wk_u32 r := let v := reg_val r in
  lazymatch v with
  | Z_to_bv 64 (Z.shiftl ?i 2 + ?A) =>
      match goal with H : u32arr _ _ A (map (Z_to_bv 64) ?l) |- _ =>
        let RD := fresh "RD" in
        pose proof (u32arr_read _ _ _ _ i (Z_to_bv 64 (Znth i l)) (Z_to_bv 64 (Z.shiftl i 2 + A)) H
                      (RF_huf_rs_cl.nth_map_Znth l i ltac:(lia)) ltac:(lia)
                      ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; lia)) as RD;
        zstep; clear RD end
  end.

Ltac wk_st32 r := let v := reg_val r in
  lazymatch v with
  | Z_to_bv 64 (Z.shiftl ?i 2 + ?A) =>
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with H : u32arr _ mm A ?l |- _ =>
        let HS := fresh "HS" in
        assert (HS : store_ok bsegs mm (Z_to_bv 64 (Z.shiftl i 2 + A)) 4 = true)
          by (apply (u32arr_store_ok _ _ _ _ i _ H); [rewrite ?length_map; lia
              | unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; lia]);
        zstep end end
  end.

Ltac wk_post := repeat first [
    match goal with H : bv_unsigned (Z_to_bv 8 ?x) = ?x |- context [bv_unsigned (Z_to_bv 8 ?x)] => rewrite H end
  | match goal with |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (FseRdKit2.sx32_small x) by lia end
  | match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (inr64_unsigned_lit x) by (unfold inr64; lia) end ].

Ltac wk_norm := rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; wk_mods.
Ltac wk_cond :=
  lazymatch goal with
  | |- negb ?c = true => apply (proj2 (Bool.negb_true_iff c)); wk_cond
  | |- negb ?c = false => apply (proj2 (Bool.negb_false_iff c)); wk_cond
  | |- bv_ltu _ _ = false => wk_norm; apply Z.ltb_ge; lia
  | |- bv_ltu _ _ = true => wk_norm; apply Z.ltb_lt; lia
  | |- bv_eqb _ _ = false => wk_norm; apply Z.eqb_neq; lia
  | |- bv_eqb _ _ = true => wk_norm; apply Z.eqb_eq; lia
  end.
Ltac wk_if_false := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota | symmetry; wk_cond] end.
Ltac wk_if_true := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true; [cbv iota | symmetry; wk_cond] end.

Ltac wk_step :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [wk_if_false | wk_if_true | if_false | if_true]
  | |- evtF ?segs _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with Some ?w =>
        let d := eval vm_compute in (decode_any w) in
        lazymatch d with
        | Some (Load SZ1 _ _ ?rs0 _, _) =>
            let rs := eval vm_compute in (bv_unsigned rs0) in
            let v := reg_val rs in
            lazymatch v with
            | Z_to_bv 64 (Z.shiftr _ 3 + 2147450880) => wk_shz rs
            | _ => first [wk_src rs | zstep]
            end
        | Some (Load SZ4 _ _ ?rs0 _, _) =>
            let rs := eval vm_compute in (bv_unsigned rs0) in first [wk_u32 rs | zstep]
        | Some (Load _ _ _ ?rs0 _, _) =>
            let rs := eval vm_compute in (bv_unsigned rs0) in first [zstep | wk_src rs]
        | Some (Store SZ4 ?rs0 _ _, _) =>
            let rs := eval vm_compute in (bv_unsigned rs0) in first [wk_st32 rs | zstep]
        | _ => zstep
        end
      end
  end; wk_post.
Ltac wk_at pcs := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := eval vm_compute in (existsb (Z.eqb pc) pcs) in
      lazymatch b with true => fail | false => idtac end
  | _ => idtac end.
Ltac wk_go pcs := repeat (wk_at pcs; wk_step).

Ltac wk_acc_hint := first [ bdtA_acc_hint
  | lazymatch goal with |- acc_in ?R (Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880), 1%nat) =>
      match goal with H : rng R (shad ?A) (nshad (?len + ?A' mod 8)) |- _ =>
        constr_eq A A'; apply (acc_shZ R A len a H); split; [lia|split; [wk_zbnd|split; [wk_zbnd|lia]]] end end
  | lazymatch goal with |- acc_in ?R (Z_to_bv 64 ?E, ?n) =>
      let nz := eval compute in (Z.of_nat n) in
      match goal with H : rng R ?lo ?len |- _ =>
        apply (rng_acc_litZ R lo len E n nz H eq_refl ltac:(lia)); split; wk_zbnd end end ].
