(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_D.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_free_A () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z;land_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6shiftlC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Malloc=F_malloc_free3sxvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge=Z_to_bv_mod64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:shiftl_1_lK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma self_word2 b3 : 0 <= b3 < 256 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (Z.land b3 31 mod 32))) = wz (sxv (2 ^ (Z.land b3 31))).
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_A ()) ["CANSEC1"] "h01bh17__arithh24__ffh38__varmaph45__with51ah62H0h71zh84__p1h94__x1h:2b3p;1p;2p;6p;7p;3p;4p;8g0000j11Tg000Uj14Tg0013j22Tg001OR0j2>Tg001jj19Tg002Oj23Tg002mj2@Tg003Gj2PTg003lj1MTg004Lj1JTg004lj1HTg005Jj1GTg005hj1aTg006Sj6]Tg0077j2=Tg007Zj7UTg008>j2TTg008`j2ETg009:j2STg009fj37Tg00:@j3RTg00:_j4QTg00;Qj2:Tg00;nj25Tg00<Nj3OTg00=5j4?Tg00=`j1LTg00>>j3KTg00>aj6;Tg00??j4ITg00?Zj1BTg00@8j1NTg00@[j2CTg00A;j2<Tg00Abj28Tg00BHj1DTg00CEj1FTg00D=j1`Tg00E;j1_Tg00E_j2^Tg00F=j2\Tg00F`j7YTg00GDj1XTg00Gfj8WTg00HJj3ZTg00Hmj2[Tg00IIj7VTg00ImR1f0R2'[p=0g00JKR3f1R4g00JiP2C?p=AP4g00KPR5g00KoR6P6g00LOR7P2g00LoFVp=6%02R8g00MOR9#1R:#1#1#1#1R;#1R<#1#1#4,22'>%99#9#9#9#4R=,34R>#0R?%4;R@,2>R>P01342#0f2RA#0%04RB'@RC[1@B813A4#0[RDf3RE/3A#0\C1P42P2n2001000000120000000X03X53PD^03^53P2PAP=p-0RDg00N4RC#MRF%JCRC%H3RG%G3RH%a3RIP5P6P6P7PIP5P6P6P7PAE]1=31RJ1=3='A,6IFU1TI7RKP2PAg00N`RLg00O@RM'E1S2A=7LMdAR314CQRMb2b3b4W8%0=,@2^8DP2%0EO1b1O3b6P3%4:RD%9:#4R:':,54122@RLX731212RNP015A4R0#01204R015EA/2AAOA42P2n2001000000120000000UX03X53P0\N^03^53P2PAP@PFPCPGPHP3PJg00O`RN1=3@R0C?,6IPKPMb2b3b4121@P2b1O3b6%L:,34PFPCPGPH1=3:,AJ,6IPKPMb2b3b4%0:P2b19K4:E;CI1>?>P313A=RA%B<R>#NR?%B;R;%49R:/C2'<,8>13E=RE,:DR=#D#FRG37X73P31:DAR11<;2,8>=7?GX73P?1<;1RG,8>RO1<;=,8>=7?2X0?1E?O%4<,:D,5G,8>%`GE;%D1#F97?Oe1C:A%_AE;15A@PFPC1^34PHPIP5P6P6P7PIP5P6P6P71\39R9,AJ,6IP3P9PNP0C?,6IFYRI%X6PIGWPKPMb2b3b4X931>8L124@,>B[^93P2PEP4O2b19ZA@E;b6UX:3P2O1X:3o"). Qed.

End CANSEC1.
