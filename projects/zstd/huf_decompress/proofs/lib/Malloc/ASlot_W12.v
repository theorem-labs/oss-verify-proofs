(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3 ASlot_W1 ASlot_W10.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W12 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib6Malloc>F_malloc_entry5stc_qC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z7div_modI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC35stdpp7tactics<f_equal_helpK46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib6Malloc>F_malloc_entry?size_to_class_qC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr05I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.

Lemma stc_q_eq : j = stc_q (szc * cnt).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W12 ()) ["CANSEC1"; "STC"] "h04__x1h14__x2h27__arithh34__ffh44__p1h58__varmaph65__with74__x3h84__x4h95heq_jh:6heq_n'h;1Hh<2H0h=2H1h>2H2h?2H3h@1qhA1rhB1zp;1p;2p;3p;4p;6p;8p;7g0000j13Tg000Uj14Tg0013j25Tg001Pj1>Tg0025j2<Tg002Rj2hTg002oR0j1WTg003oj2HTg004Ij2^Tg004jj3FTg005Dj1[Tg005]j2zTg006=j2wTg006dj2ETg007@j27Tg007\j2ATg0087j2pTg008^j2gTg009Dj2fTg009jj1XTg00:hj1CTg00;Gj2?Tg00<0j1aTg00<Nj2OTg00<oj3`Tg00=Xj4_Tg00>9j3]Tg00>Zj2UTg00?Cj2MTg00?oj2STg00@[j1ZTg00A;j3NTg00A[j1yTg00B;j2RTg00BYj1xTg00C7j4QTg00CUj1vTg00D3j1rTg00D^j2YTg00EAj4LTg00Elj1qTg00FNj2KTg00G1j6oTg00GUj3DTg00H8j2iTg00HZj2jTg00IFj3kTg00Iej4lTg00JWj8eTg00K4j6mTg00KXj2nTg00Lbj6dTg00M@j3ITg00Mij2cTg00NRj3GTg00O;j7bTg00O_j7sTg00PCj8tTg00Pgj3uTf0R1#3#3p=0g00QJR2f1R3;F1p=8AI231p=V1c21p==AG231p=6f2R4AG2315G2p=TAG243=I21p=2AI2319I24p=\1Y21p=@P3g00QhR5g00RGR6P6g00RgR7P1g00SGFbp=1P2P3g00SgP1CLp=;P4P5P6P6P7P3P1Fsp=Jf3R8P5P6P6P7P4P3P1Gtp=:P2P3g00TNP1CLp=PAu231p=B%>1#>p=9P2p,3szcR9g00U5R:#3R;#3R<#0R=#4R>'5p,3cntR?'5%>:R@#0#4RA'<RB%4@RC'<RD/h>RE#W159?RF#WRG,81XB2P2P2P0P0PEPFP2\2/H01^D>g00UZR09F2>RF#[15>E1zD>RH'<,8D[1wD>1E0>RI170H1EH>'A[1pD>1E>01E>H17H0'A[1gD>AF2E0\F1fD>18HD\FPEP2PHP2p,2n'RH#XRE,H2p,1jRD/8EREeRJPE1H2B18HBRHeRKPHg00V8RLg00VdRM#CRN#CRO#CRP#CRQ#C,?2RR%a:,O21?2PRP5`2'V%4;#=RS1?2MRM1?2ORO'6P2%4:RT,O2P:1O20C_RU9]2:,U2RV/6MRW1?2NRN,6VATSON92PP3\32g00WCRX'M'S1?2QRQ/VPRY/6N%=>RZ16OOR[%3=R=#4R\#=?TNM52Z72W92VY52S/MX%ZLRS5NL3N%yLRVP2P2f4RW,R2P4%x2RZCQP31R28CQ%v2RN%r2R]P]P21Y20R^g00WoR_%@>R`CL,1]%q6Ra1K2<R<,;^,1]P2P<P_P`CL,1]5J]C:PaP]P]P]P5P6P6P71P`^,1]EoPa1K2;R;/B`1K2@R_'B%@ARb5D2%@C5D21K2:R:,B`=D2<'P,1]C:PaP]%@TR</;;,1]Rc%9@#9R@#9#9#9Rd#>#4Re#@Rf,;;,1]5J]Pa1B;_,P:,1]C:C:C:1i]7R_P1P4g00XVRgg00Y6Rh'H1j14=FghdAk203ClRhb3b5b6X02X12X72X82170W1EW>'A\Ig00YV\F158>/5W/<ARA/<C15>4f5RC'<'8[17T8178e'A15WC,88[[[^02^12^72^82P1P8P?P9PWf8f9p,3SZCRCO7b2b:b9bAb@b?b>b=b<b;Ge%XBPJPEPKPHp-0RH%3d#0#0#4#=Rd1U2U/6Q%=e16PR%3@#9#9#3#9#3#0#0#>#0#0R@#>#3#0#0#4#=16OM%3@#>#0#0#4#=A2PQY,6O16d[32323232/MX,SM=NLSPVP21R24P3PZCQPNP]1B:`/B;R;=D2`%0=#0#0#4R=#@';,1]PaP]P]P5P6P6P7PWEm9J]cPaP]1;<:,1]1;:f,1]5J]PaAD2;b,;^,1]C:C:C:P_Phb3b5b6X02X12W4151>/53/<>/7=17T4RT/A8174e,AT170A[[[^02^12^4HP117?\P?P9p,5SMALLp,2CRPCO6b2b:b9,nBEd18DGeo"). Qed.
End STC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nest_frame (j gm cnt size sc : Z) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (wz j); C8 (Z_to_bv 64 gm); C8 (wz cnt); C8 (wz cnt); C8 (wz size); C8 (Z_to_bv 64 (sc + 58)); C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

End CANSEC1.
