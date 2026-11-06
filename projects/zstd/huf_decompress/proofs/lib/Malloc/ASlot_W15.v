(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 F_malloc_bigw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W15 () := "C56Stdlib6ZArith6BinInt1Z3b2zK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z4lxorC47Corelib4Init9Datatypes4negbI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4bool00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr04C45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib7ZBridge9zb_signedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z8leb_spec".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma lxor_b2z_1 b : Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W15 ()) ["CANSEC1"] "p'0h01bi001bp;1p;2p;3g0000j10Tg000Mj15Tg000kj23Tg001Ij11Tg001gj34Tg002Aj22Tg002[R0P0g003;R1f0R2#0g003Y#5'3%12#034P2g004>#1#0,21g004^#1#0,21n0110000020000X00P2O1W0o"). Qed.

Lemma signed_lit_small z : -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W15 ()) ["CANSEC1"] "p'0h02Hah14__p1h24__x1h34__x2h44__x3h51zh61Hh72H0h82H1h92H2h:2H3h;2H4h<7__arithh=4__ffh>6__sat5h?6__sat6h@6__sat7hA6__sat8hB8__varmaphC5__withD1qhE1rhF2HzhG1bi001bhH2b0p&0p;1p;2p;3p;4p;6p;7p;8g005>j10Tg000Mj1ATg005cj1?Tg006Hj2NTg006ek102Tg007Bj27Tg007^j21Tg008:j2<Tg008Uj1QTg0093j2\Tg009Yj2[Tg00:Cj2=Tg00:`j2@Tg00;=j2{Tg00;cj25Tg00<Cj2qTg00<eR0j3pTg00=Ij2kTg001gj3CTg00=jj1hTg00>Cj2JTg00>`j2TTg00?=j2VTg00?Zj2aTg00@Aj2_Tg00@hj2^Tg00ANj2]Tg00B4j2OTg00B\j3MTg00C@j1:Tg00C_j2LTg00DHj2YTg00E1j3XTg00EZk101Tg00F8k200Tg00FYj3WTg00GBj2FTg00Gnj2>Tg00HZj1~Tg00I:j3BTg00IZj1zTg00J:j2UTg00JXj4vTg00K6j1uTg00KTj1tTg00L?j2STg00Lbj3RTg00MEj1oTg00Mgj2KTg00NJj6jTg00Nnj6iTg00ORj3lTg00P5j3mTg00PXj2nTg00Q;j2gTg002Aj2fTg00Q]j2eTg00RIj3dTg00Rhj4rTg00SZj3sTg00T=j2cTg00Tlj6PTg00UJj2wTg00V2j1xTg00Vlj3yTg00WUj4GTg00X@j7`Tg00Xdj7|Tg00YHj8}Tf0R1#0#0#0#0p=bg003;R2f1R3;C1p=6g00YlR4/71p=81L21p=;Ay231p=2%01#0p=Z%01#0#0#0#0#0#0#0p=9P2P3g00ZJP1CGp=DP3g00[1R5g00[PR6P6g00\0R7P1g00\PF`p=4P2P3g00]0P1CGp=If2R8P5P6P6P7P3P1F|p=Hf3R9P5P6P6P7P8P3P1G}p=3P2P3g00]WP1CGp=Eg003YR:#0R;#AR<%?:R=#?#?#?#?R>#AR?'NR@$02RA/71111@'<P2g002[RBP2%0;#bRC#QRD1\D3RE'[RF/=@PF%ACRG,N<RH,@Fn01000000200001618X52P21{D3RIPBP21=1@P11@1Hn0100000020000/68X52153HRJ/q@11J@17@J1=J@3p158H/=@PBP0159HR0/1@17@0PBP2P3f5R0/5HRJ1@JHn0100000020000/60P3f4RJ/5HRK/1@1k0HRLAC2H4RM#hf6RN1JNH,TH15NH'V'6[RO1aNHRP114HRQf7RR/5HRS#811SH'<[RS1_RHRR11H4f8RT/5HRU,1H17U4'<[RU1^THRTf9RV/JH=C24\MRW1]VHRVf:RX/5H/6X\MRY1JXHRZP2f;R[/5HR\P21O<?R]114<R^%8?114@[[R_%8<R`g00^>RaAM<?3UW0R?%8@\a^0`Rb1O<GRc%8GPQ[\^R^AM<G3VaX0`RG%8H\a^0`R`p-0Rag00^ZRdg00_FRe#:Rf#:Rg#:Rh#:Ri#;Rj1L2eRe'2Rk%ZC#9#9#9#9#9#9#9#A,Y2=X2eRC%:iRi#:#;Rl&01:-002Rm%;iRi5W2Rn%;gRg'2'2'2g00_eRo'F'>AW2mj/2eRm%;hRh,2j,2i%;f/2e/Fo'>'>%~dRe5Bd3B%zdRfP21U28P31U29CvRp%u2Rq%t2RrPr1S24Rs1S2<R<=R2DRt'D,4rRu%o6Rv1K2:R:,Is,4rPrP5P6P6P7P0EjRw5HrC3PvPrPrPrP5P6P6P71Ets,4rEiPv1K2;R;1K2=9l2t=m2:'E,4rC3R=PvPr%Q>9R2<R<,D:,4rPvPr1n2</I;,4r1D;<,4r5HrR>Pv1E:;,4rC3C3C3C31gr7R7P1P8g004>Rs,fB1e18=CBsdAd243CrR4b=bBbCX22X32X42W1%83/<J\Qg00`Q\M1THJ/V8,69[R9118@17AJ11J@'<RA16J0[[[[^22^32^42^1aP1110HPNfARMP0PXP[f<Rsf@R6O8b<b>b?b@bAbEbDb;b:b9b8b7W6P1O117@KPLPOPPPSPRPUPTPWPVPYPZP2P\P2P]P_P?PbPcP^PGP`12jg,2n,2C/Fo,>k12ih,2l,2C/Fo,>m=Bde5BdPfPpPqPrPrPuPv1D:t,4r9HrwC3PvPrP=PvPr1I<:,4rPvPrP>PvAs2:t/E;,4rC3C3C3C3P7P4b=bBbCX22X32X42X1a113H,<J\Q17@81@JH/60\A[\9[^22^32^42^1aP1%80PNPMP0PXP[PsP6O8b<b>b?b@bAbEbDb;b:b9b8b7W6P1O1n200210000000021100011000bHbGPBP21=I@PI1@IHn0100000020000/63ePF1cD3EP1wDE%xEEPWFX52P1O1X52o"). Qed.

Lemma ltb99_leb100 b : (99 <? b) = (100 <=? b).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W15 ()) ["CANSEC1"] "p'0h02H0h14__p1h24__x1h32b0h42b1h51Hh67__arithh74__ffh88__varmaph95__with:1bi001bp;1p;2p;3p;4p;6p;7p;8g005cj17Tg005>j13Tg000Mj1<Tg00<Cj2@Tg007^j20Tg007Bj21Tg00:Cj2;Tg00<eR0j38Tg00`nj2=Tg001gj32Tg00aKj2?Tg002Aj29Tg00HZj1>Tg00IZj1MTg00J:j2LTg00K6j1KTg00KTj1ITg00Mgj2HTg00L?j2:Tg00WUj44Tg00MEj1ETg00NJj6DTg00Q;j2CTg00Q]j2BTg00RIj3FTg00Rhj4GTg00X@j7ATg00YHj8JTf1R1g00[1R2g00[PR3P3g00\0R4f0R5g00\PFAp=6f3R6P2P3P3P4f2R7P1P5GJp=5g003;R8g003YR9#7#3#3R:#3#7#7#<R;/@510;5115;1;;5381;;1g002[R<P010;7117;%7:#3#3#<R:f4R='=R>92<1P110;61?:=R?11:=10=:;8>R>f5R=,=:R@P<P0f6RA,1:RB10A:RAg004>RC=2<1P1f7RD,1:RE19<CRFW0P5O110D:RDp-0RGg00^ZRH#>RI%MHRH1L81RJ%K8RK%I8RLP81H89R9g00ZJRM1:8:RNC4,6L%E3ROPLP81:8;RPPMP9C4,6LPOPLP2P3P3P4P6EDR3C5C51CL4R4P5P7PF1B57=2<Cdg00Yl=F81CGR7b7b8b9X28W1105:10;1P6[[^28^1GP5g004^RF92<Cf9R2P1P=O4b6W0P5O1n200210000000021000010000b4b3W5P5O1116;P?P>P@P<P0PBPAA2<F1P1PIPHPJPKPLP8PNg00]0RNP9C4,6LPOPLP8P9PNPPC4,6LPOP3C5C5P4P7b7b8b9X28X1G11:5111;P6[[^28^1GP5A2<FCP2P1P=O4b6X0EP5O119<FX0DP5O1n200210000000021000010000b4b3W5P5O1n200210000000021100011000b4b3X:8P5O1W:o"). Qed.

Section SEQ.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

Definition seqW : list (Z * Z) := [(CTX + 848, CTX + 913)]%Z.
End SEQ.


End CANSEC1.
