(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry MallocTree MallocKit_A.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocKit_AB.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocKit_A3 ASlot_W1 ASlot_W10.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_ASlot_W12 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC69OSSVerify5KrLib2CJ1A>F_malloc_entry5stc_qC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z7div_modI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC35stdpp7tactics<f_equal_helpK46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib2CJ1A>F_malloc_entry?size_to_class_qC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr05I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.

Lemma stc_q_eq : j = stc_q (szc * cnt).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W12 ()) ["AC_1"; "STC"] "h04__x1h14__x2h27__arithh34__ffh44__p1h58__varmaph65__with74__x3h84__x4h95heq_jh:6heq_n'h;1Hh<2H0h=2H1h>2H2h?2H3h@1qhA1rhB1zp;1p;2p;3p;4p;6p;8p;7g0000j13Tg000Uj14Tg0013j25Tg001Pj1>Tg0025j2<Tg002Rj2hTg002oR0j1WTg003mj2HTg004Gj2^Tg004hj3FTg005Bj1[Tg005[j2zTg006;j2wTg006bj2ETg007>j27Tg007Zj2ATg0085j2pTg008\j2gTg009Bj2fTg009hj1XTg00:ij1CTg00;Hj2?Tg00<1j1aTg00<Oj2OTg00=0j3`Tg00=Yj4_Tg00>:j3]Tg00>[j2UTg00?Dj2MTg00@0j2STg00@\j1ZTg00A<j3NTg00A\j1yTg00B<j2RTg00BZj1xTg00C8j4QTg00CVj1vTg00D4j1rTg00D_j2YTg00EBj4LTg00Emj1qTg00FOj2KTg00G2j6oTg00GVj3DTg00H9j2iTg00H[j2jTg00IGj3kTg00Ifj4lTg00JXj8eTg00K5j6mTg00KYj2nTg00Laj6dTg00M?j3ITg00Mhj2cTg00NQj3GTg00O:j7bTg00O^j7sTg00PBj8tTg00Pfj3uTf0R1#3#3p=0g00QIR2f1R3;F1p=8AI231p=V1c21p==AG231p=6f2R4AG2315G2p=TAG243=I21p=2AI2319I24p=\1Y21p=@P3g00QgR5g00RFR6P6g00RfR7P1g00SFFbp=1P2P3g00SfP1CLp=;P4P5P6P6P7P3P1Fsp=Jf3R8P5P6P6P7P4P3P1Gtp=:P2P3g00TMP1CLp=PAu231p=B%>1#>p=9P2p,3szcR9g00U4R:#3R;#3R<#0R=#4R>'5p,3cntR?'5%>:R@#0#4RA'<RB%4@RC'<RD/h>RE#W159?RF#WRG,81XB2P2P2P0P0PEPFP2\2/H01^D>g00UYR09F2>RF#[15>E1zD>RH'<,8D[1wD>1E0>RI170H1EH>'A[1pD>1E>01E>H17H0'A[1gD>AF2E0\F1fD>18HD\FPEP2PHP2p,2n'RH#XRE,H2p,1jRD/8EREeRJPE1H2B18HBRHeRKPHg00V7RLg00VcRM#CRN#CRO#CRP#CRQ#C,?2RR%a:,O21?2PRP5`2'V%4;#=RS1?2MRM1?2ORO'6P2%4:RT,O2P:1O20C_RU9]2:,U2RV/6MRW1?2NRN,6VATSON92PP3\32g00WBRX'M'S1?2QRQ/VPRY/6N%=>RZ16OOR[%3=R=#4R\#=?TNM52Z72W92VY52S/MX%ZLRS5NL3N%yLRVP2P2f4RW,R2P4%x2RZCQP31R28CQ%v2RN%r2R]P]P21Y20R^g00WnR_%@>R`CL,1]%q6Ra1K2<R<,;^,1]P2P<P_P`CL,1]5J]C:PaP]P]P]P5P6P6P71P`^,1]EoPa1K2;R;/B`1K2@R_'B%@ARb5D2%@C5D21K2:R:,B`=D2<'P,1]C:PaP]%@TR</;;,1]Rc%9@#9R@#9#9#9Rd#>#4Re#@Rf,;;,1]5J]Pa1B;_,P:,1]C:C:C:1i]7R_P1P4g00XURgg00Y5Rh'H1j14=FghdAk203ClRhb3b5b6X02X12X72X82170W1EW>'A\Ig00YU\F158>/5W/<ARA/<C15>4f5RC'<'8[17T8178e'A15WC,88[[[^02^12^72^82P1P8P?P9PWf8f9p,3SZCRCO7b2b:b9bAb@b?b>b=b<b;Ge%XBPJPEPKPHp-0RH%3d#0#0#4#=Rd1U2U/6Q%=e16PR%3@#9#9#3#9#3#0#0#>#0#0R@#>#3#0#0#4#=16OM%3@#>#0#0#4#=A2PQY,6O16d[32323232/MX,SM=NLSPVP21R24P3PZCQPNP]1B:`/B;R;=D2`%0=#0#0#4R=#@';,1]PaP]P]P5P6P6P7PWEm9J]cPaP]1;<:,1]1;:f,1]5J]PaAD2;b,;^,1]C:C:C:P_Phb3b5b6X02X12W4151>/53/<>/7=17T4RT/A8174e,AT170A[[[^02^12^4HP117?\P?P9p,5SMALLp,2CRPCO6b2b:b9,nBEd18DGeo"). Qed.

End STC.

Definition nest_frame (j gm cnt size sc : Z) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (wz j); C8 (Z_to_bv 64 gm); C8 (wz cnt); C8 (wz cnt); C8 (wz size); C8 (Z_to_bv 64 (sc + 58)); C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

End AC_1.
