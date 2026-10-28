(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Export AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AProto () := "C47Corelib4Init5Logic8eq_ind_rI5ARocqVerifyHarness?AgentSubmission3Lib5ITree5itree00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed:aembed_retC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z=add_le_mono_lK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z;div_le_monoC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI47Corelib4Init5Logic3and00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z9div_add_lC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z8add_commK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Peano2ltK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF5fp_okC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula05C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC5ARocqVerifyHarness?AgentSubmission4LibA8AcctCore7page_okC56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic6eq_indc5ARocqVerifyHarness?AgentSubmission5BothW6AProto5fp_bwC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintc5ARocqVerifyHarness?AgentSubmission5BothW6AProto6fstepSC5ARocqVerifyHarness?AgentSubmission4LibA6NodesA6fstepAC56Stdlib6ZArith6BinInt1Z4landC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5fp_leI5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node00C5ARocqVerifyHarness?AgentSubmission3Lib5ITree4respI47Corelib4Init5Logic4True00c5ARocqVerifyHarness?AgentSubmission5BothW6AProto=MAP_NORESERVEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_READC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi:PROT_WRITEC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node01K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node02K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node03K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node04K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node05K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node06K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node08K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node09K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node0:C47Corelib4Init5Logic5proj1K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node0;K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node0<K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node0=K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node07C5ARocqVerifyHarness?AgentSubmission4LibA6NodesA9fstepA_idK47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission4LibA6NodesA:fstepA_rngC5ARocqVerifyHarness?AgentSubmission4LibA6NodesAAfstepA_mmap_grantC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6aembedC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA5implFC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA6epostFC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA<implF_ret_okC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFI6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc00K6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc02K5ARocqVerifyHarness?AgentSubmission3Lib5ITree5itree01C5ARocqVerifyHarness?AgentSubmission4LibA6NodesA8at_nodeAC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPK5ARocqVerifyHarness?AgentSubmission4Spec5STree5stree01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl3aev00".
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof.
ltac2:(KReplay.run1 (kr_t_AProto ()) ["CANSEC1"] "h07__arithh14__ffh28__varmaph35__with44__x1h54__x2h61mh71nh81ph91zh:1Hh;2H0h<1ah=1bp;2p;1p;3p;4p;8p;5p;6p;7p-1g0000R0p4p710R1p9p1000Np4p710P1p8p1001Dp4p7210P1p8g002Bj20Tg002^j1STg003Cj16Tg003aj1?Tg004Fj2RTg004cj23Tg005@j21Tg005]j27Tg006=j3ATg006dj1@Tg007Dj1>Tg007dj1=Tg008Bj1<Tg008`j1QTg009Kj25Tg009nj1PTg00:Lj3NTg00:oj42Tg00;Zj2MTg00<<j2LTg00<Vj2HTg00=Bj3CTg00=\j3BTg00>;j4DTg00>mj2ETg00?Ij2FTg00?gj4GTg00@Ej28Tg00@hj1ITg00AJj8JTg00Anj5KTg00BSj39TP0j6:Tg00C<j1;Tg00D4j7OTf1R0g00DXR1g00E7R2P2g00EWR3f0R4g00F7FOp=4g00FWR51004P5f2R6g00G5R7#SR8#6R9%?7R:#6R;'RR<'3R=g00GZR>/14R?176;R@,1>'0X95P5130<f3RA/3<RB,1>/0?X95g00HT1060110A1106'0[R?11461140'010A6RC[f4RD,16116A'0\CAA604P0n2001000000120000000X85X65X75P?^85^65^75P4PBP=P>PAP6P<g00HoR>#@R=%>>R>%=5RB%<5R?%Q5RCP5g00I[RE,55RFg00J91559%P:5N5C2'41MC3R:P4P6g00J`R9g00K@RG'L1H46=C9GdAB5E0CDRGb1b2b31EE<P4b0P=P>P51F56P0PBCGP?PCP1P2P2P3P51857g00K`R71858C2,4CR8%I2P8GJP:PGb1b2b3X45X5510401006[^45^55P4PAPDP6O3b0DKO4b;170;P=P>PBP?P5PFP7155;C2,4CP:PGb1b2b310E;P4b0R4990;E:P@A96;4E:%;6%;0'0eW:X=5W<o"). Qed.
Lemma shad_aligned : forall a k, 0 <= k -> shad (a + 8 * k) = shad a + k.
Proof.
ltac2:(KReplay.run1 (kr_t_AProto ()) ["CANSEC1"] "h01zh17__arithh24__ffh38__varmaph45__with54__x1h64__x2h74__x3h82Hkh91ah:1kp;2p;1p;4p;3p;6p;7g002Bj2BTg002^j1>Tg003Cj1;Tg00LGj29Tg005@j20Tg003aj1RTg004Fj2OTg004cj21Tg005]j2:Tg006dj1DTg007Dj1CTg00?Ij2ATg00?gj4TTg008Bj1STg008`j1QTg00@Ej2=Tg00Ldj35Tg00:oj4<Tg00;Zj2NTg00<<j2MTg00<Vj2LTg00=Bj36Tg00=\j3JTg00>;j4ITg007dj1HTg009Kj28Tg00MGj6GTg00Mkj4KTg0000j64Tg00NNj2FTg00O0j2ETg00BSj3?Tg00C<j1@Tg00D4j7PTg00GZR0f0R1'0p=3g00FWR2f1R3;61p=2P3g00DXR4g00E7R5P5g00EWR6P1g00F7FPp=7g00I[R7/B1P2f2R8g00G5R9#>R:#>#>#;R;/93R<'0R=%;:%R9R>#;R?'OR@'1%31RAf3RB/:?#3/08'2X02P2118@19;8,0B/1@#310A8'2X02P210<8111;#311B;R@#3/08RC'2X02P2193;RD101B/1;#3/2CX02P2118;,0312ACX02g00HoRC#DRA%CCRCP21A28P31A2BCT%S2RB%Q2REP21=29R91=2:R:1=2>R>552552g00ORRFA529>=52:C<'71NE6R:P1P8g00J`R>g00K@R9'M1L18=6>9dAJ273CIR9b2b3b4X52X62X721038,011018/03'2^52^62^72P1P@P8P0O3b110D8/1;P3P;P8PAPC%H2RDPBPEP4P5P5P6P2182;PF1827RFC<,7EEGP:P9b2b3b4A62;7g00P9[P1b1CKE4P<1F;3E4P=1E8<E41:8?PAPCPDPBP2PFg00K`182?C<,7EP:P9b2b3b41B7?P1b1R19?8?E41:=?A?=?1E4%@=%@8/03'2eW8X:2X92o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fp_bw (R : footprint) : Prop :=
  forall b (j : nat), 0 <= b -> b + Z.of_nat j <= 2^64 ->
    (forall k, (k < j)%nat -> R (b + Z.of_nat k) 1%nat) -> R b j.

Lemma fp_ok_bw : forall lz AL, fp_bw (fp_ok lz AL).
Proof.
ltac2:(KReplay.run1 (kr_t_AProto ()) ["CANSEC1"] "h01Hh13Hk0h27__arithh34__ffh48__varmaph55__with64__x1h74__x2h84__x3h94cstrh:5cstr0h;1kh<2ALh=2Hbh>2Hjh?2Hkh@2_HhA1bhB1jhC2lzhD1zp;1p;2p;4p;3p;7p;6p;<p;8g002^j13Tg009nj1iTg00PVj1ZTg00Q9j2RTg007Dj1MTg00QYR0j11Tg005@j20Tg003Cj1?Tg004Fj2VTg002Bj2>Tg00R9R1j2<Tg00RQj1;Tg00S0j4Lj2aTg00>mR2j25Tg00HTj2ITg00<<j27Tg00Sej4\Tg00TLj1HTg006dj1[Tg007dj1YTg008Bj1XTg008`j1WTg009Kj2=Tg00;Zj2UTg00<Vj2TTg00=Bj3STg00=\j3QTg00>;j4PTg00U1j4OTg00U\j26Tg00VEj38Tg00Vnj2DTg00WZj3ETg00?Ij2FTg00?gj4NTg00@Ej2CTg00@hj1hTg003aj1gTg00Ldj3JTg00:Lj3fTg00X:j7cTg00X^j1ATg00YYj3BTg00ZSj1`Tg00[4j6_Tg00[Pj1bTg00\Gl<GTg00:oj4KTg00D4j7dTg00AJj8eTg00I[R3f0R4'>p=4g00\lR5g00FWR6P1P0P2g00]KR7g00]mR8P3f3R9f2R:f1R;P4M<Gp=^P5P6P1P0P2P7f5R7f4R2P9P:P;P4M<Gp=]P6P;g00J9P4CKp=@P;g00DXR0g00E7R1P1g00EWR<P4g00F7Fdp=2P6P;g00K`P4CKp=9P9P0P1P1P<P:P;P4Gep=:g00G5R=#3R>#3#3#3#3#3R?#iR@#ZRA/RA#Mp-0\A%4;RA%1;RB,0:%?>RC%??'VR?'>1<49f7RDf6RE107B%;8RBCL[^;51<42%4E15E?'IP9P:P;P81<8B%?=RF,53RG1763PBPF176FC^1<:E%1:RH%1ERI'5RJP:PH176HPEPI176IE]P;C\RKPJ%HDRL%1D#4RM%H2RN%12#4ROg00HoRP#[RQ%MPRR%Y6%X6RS%W6RT1=63RU1=6F'@'21UT<RFP4P:g00J`RVg00K@RW'71T4:=SVWdAQ63;CPRWb3b4b5PGP4b2b:b9b1COPKPJPLPMPNPO%;BRO#;RN#;,66166B1668RB586586g00^LRM'D166N166O=86B586/DM=EPQ5EPPRP61F6:P;1F69CNPSPT1C6>R>,9U,2T%h1RSPT%g=,C6RR,@>,2TPSPT1C6=R==J6R1=6C=f6@R@'9,2TPSPT19U=,2TPSPTP0P1P1P<AJ6=>R=,9U,2T1@=@,2TFcC:C:C:C:PFPWb3b4b5X66X76X8615:910:2/>?%491027R:#415:?'I[[[\A^66^76^86P4f:RA#1PIf;RIP;P9f8R:f9R?O7b2b:b9b1O510DH%18'0#A9B?:P6%19,0:R:/03%A49BIAXD6P4P:%`:E_%A:9BA?P4b0b0W@W?X;5PEP7P2P9CLeW0W>W=XB5XA61a;4#beW<WCo"). Qed.

Lemma rng_merge : forall R lo n1 n2, fp_bw R -> 0 <= n1 -> 0 <= n2 ->
  rng R lo n1 -> rng R (lo + n1) n2 -> rng R lo (n1 + n2).
Proof.
ltac2:(KReplay.run1 (kr_t_AProto ()) ["CANSEC1"] "p'0h04__x1h14__x2h24__x3h31bh41jh54__x4h67__arithh74__ffh88__varmaph95__with:4cstrh;1Hh<3Hk0h=4__x5h>5cstr0h?4__x6h@1AhA2A1hB2A2hC1BhD2B1hE2B2hF2BWhG1GhH2HbhI2HjhJ2HkhK1LhL2N1hM2N2hN1RhO1khP2lohQ2n1hR2n2hS1si001si011lp;1p;3p;2p;4p;7p;8p;<g00[Pj1fTg00_8j36Tg002^j19Tg003Cj1GTg004Fj2\Tg002Bj21Tg00QYR0j18Tg005@j20Tg00HTR1j2>Tg006dj1NTg007Dj1eTg00?Ij2?Tg008Bj1[Tg008`j1ZTg00@Ej2=Tg003aj1JTg009Kj2CTg009nj1YTg00:Lj3XTg00@hj1WTg00;Zj2VTg00<<j2BTg00<Vj2UTg00=Bj3TTg00=\j3PTg00>;j4OTg00TLj1ATg00RQj1HTg00U\j2FTg00VEj3ITg00Vnj2QTg00WZj3RTg007dj1STg00R9R2j2MTg00_kj2dTg00>mR3j2;Tg00`RR4j2cTg00Sej4`Tg00:oj4@Tg00a2j4LTg00?gj4^Tg00Ldj3_Tg00D4j7ETg00AJj8DTg00\Gl<aTg00I[R5f0R6'1p=4f2R7f1R8'0/16p=31086,17p=<g00FWR9P7P8P6C^p=5A_986p=2P7g00DXR:g00E7R;P;g00EWR<P9P8g00K`R=P6C@g00F7R>FEp=:f5R?P:P;P;P<f4R@P:P;P;P<P9f3RAP=P7C@P>FEP8P6GDp=7g00\lR=P9P2P0P3g00]KP?P@PAP7P8P6M<ap=bP@P:P;P;P<PAP:P;P;P<P7P>FEP8P6GDp=KPAP:P;P;P<P7P8P6GDp=]g00aM%fA%47R:f6R>?6?@P1%4>g00G5R3#9R0#GR2%90RB#9#9#9#9RC#G'\RD93>?f8RE/18%88RF,07RGf9RH/0ERI'1f;RJPAP7O2[[^4=^39'>f7RK/0>RL=6E?A6HEL[P6%4E11ID11J8f<RI/0JRL,1Gf>RMPAP7O2[[^4=^39'>P1f:RN?3HD11I8f=RO=<GIf?RPPAP7O2[[^4=^3910JNRQ=6IHA6OIQ[P611LD11P8f@RL=<GPfBRQPAP7O2[[^4=^3910MO=6PIP110PMRP#4A3PODfARO/0LRR/1810QO/0LRS,1GfDRTPAP7O2[[^4=^39'>A6OLPP6%4R11SDfCRS=3T8fERR/0TRP/0SRL,1GfGRUPAP7O2[[^4=^39'>P110SQRS?3OD11P8fFRP/0RRO=<GTfHR1PAP7O2[[^4=^39A6RTSP611LDA31U8fIRL/01RS=<GUfKRRPAP7O2[[^4=^39%4UA3UODRO11L8RLfJ=<GSRSfLRGPAP7O2[[^4=^39RV'>PMPOPVg00HoRV#NRO%eVRM1?97RW1?9ARX758RY%[9RZ%Z9R[P[1=93R\1=90R]'2R^%J3R_,=9R`'21C92%YC5X9RC%W;R;12]`R2,2\=:[CE71V[<R<P6P7g00J`Rag00K@Rb'B1U67=TabdAP958CORbb7b8b9X09X19X291068Ra?37D107ARc=38D[^09^19^29P6PPPUP1P7O4b6P1PAP7%A7R1%87RU#4RPg00]mRd#HRe#H,F91F9e1F9d5I95I9g00^L'Q=RVORVPM%S9Rd95W7?58dPZP[P[1=9BRBP\P;P[P[1C95R5PBP;A:[5\E7E7P<Pbb7b8b9X09X191186P:\:[^09^19P6fMRWP?PAPTO4b6b:P1PPPVPM1?9@RP?57dR11?9??5AdRd758PZP[P[P^%J0,=9R012`BRT'2P;P[P[120`/2BPCP;A:[^CE7E7P<Pbb7b8b9X09X19X29X59X=9A<a@c10?A?3@D11cD[[^09^19^29^59^=9P6PWPRPG%8@RRP?P7PKO7b6b:1M6A10?FRF10WGRG'd1;FG11GF'cP410>URUfNR4/0WRW';11WUfP%8A,0KRWPeO2P6fO/04R4,;WPQ10ERRQPe1M@K%8KRU,;RRGP@PR1B9RPKPU1B9UEbPAC`RUPG%AERK%8ERE#4RR%A>RF%8>#4RDPVPMPYPZP[P[P5P`P;P[P[P\P]P;A:[\2E7E7P<Pbb7b8b9X09X19X29118710A@R2,17[\:^09^19^29P6PEPIfTR5P8PNO5b6b>b:b<PUPGPKPRPFPDPOPMA518XR1PZP[P[P9P^g00J9RXPTC@P;%G3R3,C9,2^RN=:[TDKP<Pbb7b8b9X09X19X29X591;ac1087RY?332[^09^19^29^59P6fSRCP5PEPIP@O5b6b>b:b<O4WKP6O1114WPHPQPePUPGPKPRPFPDPOPMP1PZP[A:[^TR^P;P^C]P<Pbb7b8b9X09X19X29X5911ac11Y2[^09^19^29^59P6PEPIPCP5P@O5b6b>b:b<PUPGPKPRPFPDPVPM1?9>95P7?58dPZP[P[P9P]PX%9_,=9R_C@P;P[P[12\_12B0,2`P;12T09:[NE7DKP<Pbb7b8b9X09X19X29X59X=9X?91;8?10@?R@,0A938>10@>93c3[[^09^19^29^59^=9^?9P6%8JfRPCP5PEPIPAPHO8b6b>b:b<O4WGP6O1n200110000021110111101bSWJXO=O5XISXHLX4=X39CLCLWCWEP8P6O2n2001000000121000000W;WDP8P6O2n2001000000121000000W;W@WBP8P6O2n2001000000121000000W;WAP8P6O2n2001000000121000000W;XM:WLWFXR9XQ9XP9WNo"). Qed.

(* [comment removed for export] *)
Definition MAP_NORESERVE : Z := 16384.

Definition fstepS (n : node) (rsp : resp) (R R' : footprint) : Prop :=
  fstepA n rsp R R' /\
  match n with
  | NMmap addr len prot flags =>
      (Z.land flags MAP_NORESERVE = 0 ->
       prot = PROT_READ + PROT_WRITE ->
       bv_unsigned (eff_ret rsp) mod page_size = 0 ->
       rng R' (shad (bv_unsigned (eff_ret rsp))) (shlen (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))))
      /\ fp_bw R'
  | NMunmap _ _ => fp_le R R'       (* [comment removed for export] *)
  | _ => True
  end.

Lemma fstepS_fstepA : forall n rsp R R', fstepS n rsp R R' -> fstepA n rsp R R'.
Proof.
ltac2:(KReplay.run1 (kr_t_AProto ()) ["CANSEC1"] "p'0h01Hh12H0h21Rh32R'h42_Hh51ni001nh63rspi014addri022bsi033bufi044bufsi054codei065counti072fdi085flagsi093leni0:4pathi0;4proti0<3reqp;4p;2p;3p;1g00bFj4BTg00c>j43Tg00d5j2>Tg005@j2ATg00=Bj39Tg002^j10Tg009nj1=Tg00dSj12Tg00eIj21Tg00f3j25Tg00C<j18Tg00fSj2<Tg00g9j1@Tg00h7j1?Tg00_8j37Tg00[Pj16Tg00HTR0j2:Tg00i0j2;Tg00FWR1f0R2g00I[39p=4g00ifR3g00j[g00aMR4f3R5f2R6f1R7P2CBP0f4R0P5P6P7C3P3p-0R8P0g00kNR9P9P9P9P9P9P9P9P9g00kj,>2#4R:g00lig00md'A9916R1g00G5#0#0#0#0#0#0#=R;f9#2'1g00n`R<'5#4f8R=f:#2,1;#8f5R>,<;,1;#@#?R?37[[[%6>':1;05P9P9n01100000=20107102201071041010:30107103106101072010710<00101051010<4010110910;108201011093010110910;20101109P>P0P5P6C3P2f6R6P>P0P5C3P3P8f7R8P9P9P9P9P9P9P9P9P9f<#2,1;/5<#4f;f=#2,1;#8;7?[\1\:%6=':1;86P9P9n01100000=20107102201071041010:30107103106101072010710<00101051010<4010110910;108201011093010110910;20101109P7W4W0P7P2O2n2001000000120000000W1X34W2W6W5o"). Qed.

(* [comment removed for export] *)
Lemma fstepS_le : forall n rsp R R', fstepS n rsp R R' -> fp_le R R'.
Proof.
ltac2:(KReplay.run1 (kr_t_AProto ()) ["CANSEC1"] "p'0h02HAh12HSh21Hh32R'h42fdi002fdh54addri014addrh61bh71jh83leni023lenh94proti034proth:3reqi043reqh;1Rh<2bsi052bsh=3bufi063bufh>4bufsi074bufsh?4codei084codeh@5counti095counthA5flagsi0:5flagshB1ni0;1nhC4pathi0<4pathhD3rspp;4p;2p;3p;1p;6g00bFj4STg00c>j40Tg00d5j2>Tg005@j2RTg00=Bj3<Tg002^j13Tg009nj1?Tg00f3j26Tg00C<j1:Tg00fSj2=Tg00eIj2;Tg00g9j1BTg00h7j1ATg00_8j35Tg00[Pj19Tg00HTR0j27Tg00i0j21Tg00PVj1QTg007Dj1@Tg00oXj2PTg0000j68Tg010Mj2MTg011Bj1LTg0127j3ITg012lj1HTg013aj2GTg014Vj1FTg015Kj1JTg016@j4KTg0175j3ETg017Pj2DTg018Ej3NTg019:j2CTg00dSj1OTg00FWR1f0R2g00I[3<p=4f1R3%O2';p=2g00ifR4g00j[g00aMR5f3R6f2R7P3P2CSP0f4R0P6P7P3C0P4p-0R8P0g00kNR9P9P9P9P9P9P9P9P9g00kjR:,>2#4R;g00lig00md'RR<9<17R=g00G5#3#3#3R>#3#3#3#?R?f9R@'2g00n`RA'6#4f8RBf:RC,2?#:f5RD,=?,;?#B#ARE35[[[%9D'71106P9P9n0110;000=20100105201001071010<3010010610910100201001040010108101044010110210310:2010110230101102103201011021167P2f6RFPDP0P6C0P4P8f7R0P9P9P9P9P9P9P9P9P9f<RG,2?/6A#4f;RHf=RI,2?#:;5E[\=\;%9B'7110FP9P9n0110;000=20100105201001071010<3010010610910100201001040010108101044010110210310:201011023010110210320101102P4P2PBP0PFC0P4P8P3P9P9P9P9P9P9P9P9P9f?R8,2?/6A#4f>R4f@RJ,2?#:;5E[\=\;%9H'711C@P9P9n0110;000=20100105201001071010<3010010610910100201001040010108101044010110210310:20101102301011021032010110211@B]1]0PB%?>#Q#@R>1P32PHPCP@C0P5PG11I2X35g00\lR;P4P3P2O2P2W2W7X6111GGePHP3E8X19R=W0W<X41P3P2O2%@>1M32PHPCP@C0P=W0W>X41P3P2O2%L2P@PBP0C0P5PC11H2X35PGP3P2O2P2W2X7;X6111CCeP@P3E8X19REW0XC>P2O1AI732PIPGPHC0P5P41182X35PJP3P2O2P2W2X7;X611144ePIP3E8X19W0X@1X=1X41P7P3P2O3%H2P@PBP0C0PEW0X41P2O11G32PHPCP@C0P=W0X:1X41P3P2O2g019oP0PFPDC0P5PB11@2X35PCP3P2O2P2W2X7;X6111BBeP0P3E8X19W0%F2P@PBP0C0PEW0X?1P2O1%J2P@PBP0C0P3X19R9W0X:1P2O1P6P7P3P2CKP8P4PIC01>3:#4A<16<R<fB,2?/6A#4RAfAR:fC,2?R0#:1=?F,;?#BR?#A35[[[%94'711J8A5:0?\A\<;E3W1W0XA1X91X81X51P6P7P3P2O41D32PHPCP@C011HCP2W1W0X81X51P3P2O2AN732PIPGPHC0P9W0X91X81X51P7P3P2O31C32PHPCP@C0P=W0X81X51P3P2O2n0110;000=20100105201001071010<3010010610910100201001040010108101044010110210310:201011023010110210320101102P3P2O2W1W0P3P2O2n2001000000121000000W2X35W;WDWBo"). Qed.

Lemma fstepS_id : forall n rsp R,
  match n with NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ => False | _ => True end ->
  fstepS n rsp R R.
Proof.
ltac2:(KReplay.run1 (kr_t_AProto ()) ["CANSEC1"] "p'0h01Hh12fdi002fdh24addri014addrh33leni023lenh44proti034proth53reqi043reqh61Rh72bsi052bsh83bufi063bufh94bufsi074bufsh:4codei084codeh;5counti095counth<5flagsi0:5flagsh=1ni0;1nh>4pathi0<4pathh?3rspp;4p;2p;3p;1g00c>j4ETg00d5j2>Tg005@j2ATg00=Bj3:Tg002^j12Tg009nj1=Tg00dSj11Tg00eIj20Tg00f3j25Tg00C<j14Tg00fSj2<Tg00g9j1;Tg00h7j1@Tg00_8j37Tg00[Pj16Tg00HTj28Tg00i0j29Tg01:dj4DTg00PVj1CTg007Dj1?Tg00a2j4BTg00FWR0f0R1g00I[3:p=3g00ifR2g00j[g00aMP2p-0R3f2R4g00kNR5P5P5P5P5P5P5P5g00P9R6P6P6P6P5n0110;000=20100105201001071010<3010010610910100201001040010108101044010110210310:201011023010110210320101102f3R7P4f1R8P8CEP2P3P7P5P5P5P5P5P5P5P5P5g00kjR9,>1#3R:g00lig00md'AR;9:04R<g00G5#2#2#2R=#2#2#2#=R>f8R?#1'0g00n`R@'5#3f9#1,0>#4f5RA,<>,0>#;#@RB57?[[[%6A'81977P5P5n0110;000=20100105201001071010<3010010610910100201001040010108101044010110210310:201011023010110210320101102P7P4P8P1CDP2P2P3P1P5P5P5P5P5P5P5P5P6P6P6P6P5n0110;000=20100105201001071010<3010010610910100201001040010108101044010110210310:201011023010110210320101102P2P3P8P5P5P5P5P5P5P5P5P5f:R3#1,0>/5@#3f;R2#1,0>#4=73B[\<\:f7R:#6'819AAP5P5n0110;000=20100105201001071010<3010010610910100201001040010108101044010110210310:201011023010110210320101102]0P7%==#C#?R=g01;^RAX05R5W7X10P8P1O2%?=P5W9X10P8P1O2P5X>=P1O1P5X;0X80X10P4P8P1O3P5X10P1O1P5X50X10P8P1O2P5P5X:0P1O1PAX06RAX50P1O1P61>49#3f4=:0;f>R;#1,0>/5@#3f?#1,0>#41<>:,0>#;#@57;[[[%62'8P1n010000000X06X<0X40X30X20P7P4P8P1O4P619::P1n010000000X06X30X20P8P1O2PAX40X30X20P4P8P1O3P5X30X20P8P1O2n0110;000=20100105201001071010<3010010610910100201001040010108101044010110210310:201011023010110210320101102P1O1CBW0W6W?W=o"). Qed.

Lemma fstepS_rng : forall n rsp R R' lo len,
  match n with NMunmap _ _ => False | _ => True end ->
  fstepS n rsp R R' -> rng R lo len -> rng R' lo len.
Proof.
ltac2:(KReplay.run1 (kr_t_AProto ()) ["CANSEC1"] "p'0h01Hh12HFh22HRh32Hnh41Rh52R'h62_Hh73leni003lenh82loh91ni011nh:3rspi024addri032bsi043bufi054bufsi064codei075counti082fdi095flagsi0:4len0i0;4pathi0<4proti0=3reqp;4p;2p;3p;1p;9g00bFj4CTg00c>j4;Tg00d5j2>Tg005@j2BTg00=Bj39Tg002^j10Tg009nj1=Tg00dSj13Tg00eIj21Tg00f3j25Tg00C<j18Tg00fSj2<Tg00g9j1ATg00h7j1@Tg00_8j32Tg00[Pj17Tg00HTR0j26Tg00i0j2:Tg01<:l9?Tg00FWR1f0R2g00I[39p=4g00ifR3g00j[g00aMR4P3p-0R5f5R6g00kNR7P7P7P7P7P7P7P7P7P7g00P9P7P7n01101000=20108103201081051010;30108104107101082010810=00101061010=4010210:10<1092010210:3010210:10<2010210:f6R8P6f4R9f3R:CCP0f7R0P8P6P9C;P3P5P0P7P7P7P7P7P7P7P7P7g00kj,>2#4R;f2R<g00lig00md'B591R=g00G5#0#0#0#0#0#0#=R>f<R?#3'1g00n`R@'5#4f;RAf=#3,1>#81<>6,1>#A#@RB32[[[f8RC#7'61:08P7P7n01101000=20108103201081051010;30108104107101082010810=00101061010=4010210010<109201021003010210010<20102100A289:A2869[P2f9R9PCP0P8C;P3P5f:R5P7P7P7P7P7P7P7P7P7f?#3,1>/5@#4f>f@#3,1>#8;2B[\=\;%7A'61:59P7P7n01101000=20108103201081051010;30108104107101082010810=00101061010=4010210010<109201021003010210010<20102100A2908P?PAP5P9PCP0P8P<P2M9?W2W6W1f1P2O2n2001000000120000000W0W3X71X81X54W4W:W9o"). Qed.

Lemma fstepS_mmap_grant : forall addr len flags rsp R R',
  fstepS (NMmap addr len (PROT_READ + PROT_WRITE) flags) rsp R R' ->
  Z.land flags MAP_NORESERVE = 0 ->
  bv_unsigned (eff_ret rsp) mod page_size = 0 ->
  rng R' (bv_unsigned (eff_ret rsp)) (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))
  /\ rng R' (shad (bv_unsigned (eff_ret rsp))) (shlen (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))).
Proof.
ltac2:(KReplay.run1 (kr_t_AProto ()) ["CANSEC1"] "h01Hh12HFh22HSh33Halh42NRh51Rh62R'h72_Hh84addrh95flagsh:3lenh;3rspp;2p;4p;3p;1p;8g005@j2GTg016@j4=Tg00bFj4BTg00c>j4>Tg00=Bj3?Tg002^j14Tg009nj1@Tg00f3j26Tg00C<j19Tg00fSj27Tg00eIj25Tg00g9j1:Tg00h7j18Tg00_8j31Tg00[Pj1<Tg00HTR0j2;Tg01=5j8FTg00<<j2ETg00a2j4DTg00d5j2ATg00dSj1CTf0R1g00kj'Ap=3g00FWR2g00I[7?1p=0f1R3%C1'5p=2g00j[g00aMR4f5R5f4R6g00lig00md'GR7f3R8C=f2R9P3P1CBP0f6R:P5P7P6C=P8P9P3C>%36#0A?277R9g00G5#4#4#4#4#4#4#@R;/25g00n`R<'6#0R=12;:R>#9f8R?,7;,5;#:R@#8516RA[[[%<3';%35#0A16>@/;A\=[P1P?f7R=P7P:C=P5P6P8C>%3=#012;?/6<#0f9R:,2;RA#9f;R@,7;,5;#:#851=[\9[%<6';P0%3?#016A<#0RAf:R0,2;R6#9f<R>,7;,5;#:RB#851?RC[\9[%<5%3:#0A1?6B/;C\A[P1%30#012;@/6<#012;>RA#9f>RC,7;,5;#:#8510[\9[%<?%3>#016A<#0f=RA,2;R<f?R?,7;,5;#:R;51@%9<%8;51@f@P?PCPAP>P@P=P1GFP8P31E27P1O3CDW3W4W7W2P3P1O2n2001000000121000000W0W1P3P1O2n2001000000121000000W0X64W5W;X92X:2X82o"). Qed.

(* [comment removed for export] *)
Lemma fstepS_mmap_bw : forall addr len prot flags rsp R R',
  fstepS (NMmap addr len prot flags) rsp R R' -> fp_bw R'.
Proof.
ltac2:(KReplay.run1 (kr_t_AProto ()) ["CANSEC1"] "h01Hh12HBh21Rh32R'h42_Hh53_H0h64addrh75flagsh83lenh94proth:3rspp;4p;2p;3p;1g016@j4=Tg00bFj4BTg00c>j4>Tg00d5j26Tg005@j2ATg00=Bj35Tg002^j14Tg009nj1@Tg00dSj12Tg00eIj20Tg00f3j28Tg00C<j19Tg00fSj2<Tg00g9j1;Tg00h7j17Tg00_8j3:Tg00[Pj13Tg00HTR0j2?Tg00FWR1f0R2g00I[35p=1g00j[g00aMR3f6R4f5R5f4R6f3R7C=f2R8f1R9P2CBP0f7R:P4P5P6C=P7P8P9C>g00kjR;,66#1g00lig00md'AR<9514g00G5#4#4#4#4#4#4#@R=%25'0g00n`R>'8#1%24,0=#9f9R?,<=,0=#;#75:6[[[%39'?%38P2P?f8R8P:P4C=P5P6P7C>16:;#1A51?<%28,0=/8>#1%2?,0=R?#9f<R7,<=,0=#;#75::[[[%36'?P0168;#1f:R0=51<18?>#1%20,0=#9f=,<=,0=#;#75:8[[[%35%34P2160;#1A517<f;#2,0=/8>#1%27,0=#9f?,<=,0=#;#75:0[[[%38P2W1W5P9P2O2n2001000000120000000W0W4P9P2O2n2001000000121000000W0X33W2W:X71X91X81X61o"). Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation implS segs RNG t Q ms := (@implF node segs (at_nodeA segs) fstepS _ RNG t Q ms).

(* [comment removed for export] *)
Ltac fstepS_transport HF :=
  lazymatch type of HF with
  | fstepS ?n ?rsp ?RNG ?RNG' =>
      let HA := fresh "HFA" in
      destruct HF as [HA HF]; cbn [fstepS] in HF;
      first [ (* [comment removed for export] *)
              lazymatch eval hnf in (fstepA n rsp RNG RNG') with RNG' = RNG => idtac end;
              let E := fresh in assert (E : RNG' = RNG) by exact HA; subst RNG'; clear HA; try clear HF
            | fstep_transport HA; try match type of HF with True => clear HF end ]
  end.
Tactic Notation "fstepS_intro" ident(rsp) ident(RNG') ident(a) ident(HF) ident(Hdec) :=
  intros rsp RNG' a HF Hdec; fstepS_transport HF.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma implS_ret : forall RNG {R} (r : R) (Q : R -> footprint -> machine_state -> Prop) ms,
  evtF bsegs RNG (Q r RNG) ms -> implS bsegs RNG (aembed ATOP (SRet r)) (epostF Q) ms.
Proof. intros RNG R r Q ms H. rewrite aembed_ret. apply implF_ret_ok. exact H. Qed.
End CANSEC2.
