(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg AProto ABase ARep ALayout AHeapP ARepQ ARepQP ASec ASecFrame
     ADepot_iface F_adepot AFake_iface AFake_arep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AInstance () := "C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW8F_adepot<adepot_ifaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ASec7ASEC_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:AFake_arep2AHC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib5AsanW4ARep6aholes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ5AQUARC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib5AsanW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP>quar_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP9quar_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecFrame=asec_hs_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP=sec_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP8sec_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<ADepot_iface9adi_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8ah_depotC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C47Corelib4Init5Logic3notC59OSSVerify5KrLib5AsanW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5AsanW5ABase8al_storeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib5AsanW;AFake_iface5AFAKEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP>fake_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AFake_iface;afake_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7ah_fakeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6abkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6ablock01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC59OSSVerify5KrLib5AsanW;AFake_iface<afake_blocksC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW6AHeapP:ahole_laws01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AInstance3AHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQP;AQUAR_frameC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4ARep5aconc00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib5AsanW5ABase6ablock00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW6AHeapP:ahole_laws00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AInstance8AHI_lawsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW9AInstance6AHI_eqC1?~~~~~~~~~~~~~~~".
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
ltac2:(KReplay.run1 (kr_t_AInstance ()) ["CANSEC1"] "h01Lh11mh21Wh32m'h42LBh52HFh63LB'h71Xh82X'h92sth:3st'h;2EQh<1Fh=2MUh>2UTh?2WMh@1ahA1chB2ivhC1np;1p;5p;3p;4p;2p;:p;7g006:j12Tg006_j1<Tg007=j1;Tg007`j1ZTg008Bj1ATg008bj5=Tg009Yj3JTg00:Mj3ITg00;Aj3HTg00<Aj4GTg00=<j1ETg00>>j5BTg00?4j3YTg00@3j2UTg001Cj1TTg00@mj2RTg00Anj3>Tg00Bfj2QTg00CFj3NTg00Ccj28Tg00D?j3MTg00D\j25Tg00E8j23Tg00ESj16Tg00F1j17Tg00FVj1:Tg00Foj1KTg00Ghj2?Tg00HEj1FTg00I>j3LTg00I_j4@Tg00J[j2OTg00K[l:PTg00L]j49Tg00MTj1DTg00NMj3STg00OFj3CTg00O]j2XTg00P6j7WTg00Q9j7VTf0R0#2#2p=0%70#2p=1%20#7p=4p,2rcR1g00R7R2g00Rog00SlR3g00TfR4g00UaR5g00VXR6#2#0R7#2#0R8#<#;%<7#;#Z[R7g00W=#AR9P2f7R:f6R;f4R<f2R=D=f1R>f3R?;J=R@g00Wo?I<?RAf:RB?H:?PBf9RCf8RDP:CGP2f<REPBPDP;D=[[[[[]2^37]1^85]7^:4]9]0e%E1P2P:P;P<P=DBAY1B?1UBCP2PEPBPDP;DB[[\A\@[^29^37^17^85^75^:4^94^03e%T1,R1A>2?=g00XdR4/Q4R5AN44>/80AM44>,50'3%16#0#1#4#1#0#4#0#1#0#6/8>%46#7#7#4#1#4#1#0#1#4#0#0#6,5>'3#:%KCR6/8>%08#0#0#0#0#0#0R8#6,?6,5>'3#:%FCRC/8>%28#0#6,?C,5>'3#:'3'3[^@4XB5;L?f5R59>2:[\A\@[^29^37^17^03eg00YBRC#AR8P1P<P?P=C@1O:?R6P1PDP:P;P5P<P?P=P>P0M:PW>X?AX=@W5X29X37X17W4X03P2P<P?P=C9P2PDP:P5C9\6\A\@[^29^37^17^48^03eP1P?P=P0C@%D=?S>0R9=CC5ACC9;'X^C4^<4^A4R4P1P5P<P?P=P>P0FWW;W5X17X68X48X03P2P?P=P0C9P2P5P?P=C9\4[^17^68^48^03eFVo"). Qed.

Corollary AH_laws : ahole_laws (AH adepot_iface AQUAR ASEC_of).
Proof.
ltac2:(KReplay.run1 (kr_t_AInstance ()) ["CANSEC1"] "h01ap;2p;1p;4p;6g00Z;j24Tg001Cj13Tg002Cj10Tg003:j41Tg0000j62Tg004LR0g00R7p,2rcR1f0'4X00g00[9P1%31g005D%01C1g00\6E2o"). Qed.
End CANSEC1.
