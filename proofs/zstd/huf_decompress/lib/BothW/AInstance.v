(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ARep ALayout AHeapP ARepQ ARepQP ASec ASecFrame
     ADepot_iface F_adepot AFake_iface AFake_arep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AInstance () := "C47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC5ARocqVerifyHarness?AgentSubmission5BothW8F_adepot<adepot_ifaceC5ARocqVerifyHarness?AgentSubmission5BothW4ASec7ASEC_ofC5ARocqVerifyHarness?AgentSubmission5BothW:AFake_arep2AHK47Corelib4Init5Logic2eq01I5ARocqVerifyHarness?AgentSubmission5BothW4ARep6aholes00C5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ5AQUARK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothW4ARep7ah_quarC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP>quar_untouchedC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP9quar_sameC5ARocqVerifyHarness?AgentSubmission5BothW9ASecFrame=asec_hs_frameC5ARocqVerifyHarness?AgentSubmission5BothW4ARep6ah_secC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP=sec_untouchedC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP8sec_sameC5ARocqVerifyHarness?AgentSubmission5BothW<ADepot_iface9adi_frameC5ARocqVerifyHarness?AgentSubmission5BothW4ARep8ah_depotI47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8al_nodesC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8al_storeI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5BothW;AFake_iface5AFAKEC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP>fake_untouchedC5ARocqVerifyHarness?AgentSubmission5BothW;AFake_iface;afake_frameC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7ah_fakeK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC5ARocqVerifyHarness?AgentSubmission5BothW;AFake_iface<afake_blocksK5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP:ahole_laws01c5ARocqVerifyHarness?AgentSubmission5BothW9AInstance3AHIC5ARocqVerifyHarness?AgentSubmission5BothW6ARepQP;AQUAR_frameI5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00I5ARocqVerifyHarness?AgentSubmission5BothW4ARep5aconc00K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00I5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP:ahole_laws00c5ARocqVerifyHarness?AgentSubmission5BothW9AInstance8AHI_lawsc5ARocqVerifyHarness?AgentSubmission5BothW9AInstance6AHI_eq".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AHI : aholes := mkAHoles AQUAR ASEC_of (ADEPOT adepot_iface) AFAKE.

Lemma AHI_eq : AHI = AH adepot_iface AQUAR ASEC_of.
Proof.
ltac2:(KReplay.run1 (kr_t_AInstance ()) ["CANSEC1"] "p;1p;4p;2p-1p10000p4p710R0p9p1000Lp4p70P0p8g001Cj13Tg002Cj12Tg003:j40Tg0042j21Tg004Lp,2rcR0%30g005D%20C0'1o"). Qed.

Theorem AHI_laws : ahole_laws AHI.
Proof.
ltac2:(KReplay.run1 (kr_t_AInstance ()) ["CANSEC1"] "h01Lh11mh21Wh32m'h42LBh52HFh63LB'h71Xh82X'h92sth:3st'h;2EQh<1Fh=2MUh>2UTh?2WMh@1ahA1chB2ivhC1np;1p;5p;3p;4p;2p;:p;7p-1p10000p4p710R0p9p1000Lp4p70P0p8g006:j11Tg006_j1<Tg007=j1;Tg007`j1ZTg008Bj1ATg008bj5=Tg009Yj3JTg00:Mj3ITg00;Aj3HTg00<Aj4GTg00=<j1ETg00>>j5BTg00?4j3YTg00@3j2UTg001Cj1TTg00@mj2RTg00Anj3>Tg00Bfj2QTg00CFj3NTg00Ccj28Tg00D?j3MTg00D\j27Tg00E8j24Tg00ESj10Tg00F8j16Tg00FVj1:Tg00Foj1KTg00Ghj2?Tg00HEj1FTg00I>j3LTg00I_j4@Tg00J[j2OTg00K[l:PTg00L]j49Tg00MTj1DTg00NMj3STg00OFj3CTg00O]j2XTg00P6j7WTg00Q9j7VTf0R0#1#1p=3%00#1p=5%10#1#1#1p=2p,2rcR1g00R7R2g00Rog00SlR3g00TfR4g00UaR5g00VXR6#1#3R7#1#3R8#<#;%<7#;#Z[R7g00W=#AR9P2f7R:f6R;f4R<f2R=D=f1R>f3R?;J=R@g00Wo?I<?RAf:RB?H:?PBf9RCf8RDP:CGP2f<REPBPDP;D=[[[[[]2^37]1^85]7^:4]9]0e%E1P2P:P;P<P=DBAY1B?1UBCP2PEPBPDP;DB[[\A\@[^29^37^17^85^75^:4^94^03e%T1,R1A>2?=g00XdR4/Q4R5AN44>/80AM44>,70'4%56#3#0#5#2#0#0#0#3#5#3#6/8>%16#0#0#5#0#0#0#2#0#2#0#2#6,7>'4#:%KCR6/8>%38#2#2#2R8#6,?6,7>'4#:%FCRC/8>%18#3#6,?C,7>'4#:'4'4[^@4XB5;L?f5R59>2:[\A\@[^29^37^17^03eg00YBRC#AR8P1P<P?P=C@1O:?R6P1PDP:P;P5P<P?P=P>P0M:PW>X?AX=@W5X29X37X17W4X03P2P<P?P=C9P2PDP:P5C9\6\A\@[^29^37^17^48^03eP1P?P=P0C@%D=?S>0R9=CC5ACC9;'X^C4^<4^A4R4P1P5P<P?P=P>P0FWW;W5X17X68X48X03P2P?P=P0C9P2P5P?P=C9\4[^17^68^48^03eFVo"). Qed.

Corollary AH_laws : ahole_laws (AH adepot_iface AQUAR ASEC_of).
Proof.
ltac2:(KReplay.run1 (kr_t_AInstance ()) ["CANSEC1"] "h01ap;2p;1p;4p;6p-1g0000R0p4p710R1p9p1000Lp4p70P1p8g00Z;j24Tg001Cj13Tg002Cj10Tg003:j41TP0j62Tg004LR0g00R7p,2rcR1f0'4X00g00[9P1%31g005D%01C1g00\6E2o"). Qed.
End CANSEC1.
