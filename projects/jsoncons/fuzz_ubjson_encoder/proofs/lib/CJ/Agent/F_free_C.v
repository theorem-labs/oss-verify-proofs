(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_mm_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_D.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_F_free_C () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem4sx32C13~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free;swrap32_eq'C13~~~C47Corelib4Init5Logic8eq_ind_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free;mod64_mod32C13~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9le4_congrC13~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


Lemma le4_sx32 (v : word) : le4 (sx32 v) = le4 v.
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_C ()) ["CEIL_WRAP_1"] "h02Hah12H0h23H10h32H5h47__sat15h57__sat17h64__x1h74__x2h84__x3h94__x4h:4__x5h;4__x6h<4__x7h=1vh>1zh?1Hh@2H1hA3H11hB3H12hC3H13hD2H2hE2H3hF2H4hG2H6hH2H7hI2H8hJ2H9hK7__arithhL4__ffhM7__sat14hN7__sat16hO8__varmaphP5__withQ1qhR2q0hS2q1hT1rhU2r0hV2r1hW1up&0p;1p;2p;3p;4p;6p;7p;8g0000j13Tg000Uj1QTg0013j1iTg001Vk105Tg002`j2JTg003Jj2xTg0041j2tTg004Wj1FTg0055j2OTg005Rj20Tg0062j1@Tg006Wj21Tg0074j2NTg007Uj1}Tg007nj24Tg008Kj2ATg008hj2RTg009Oj2:Tg009kj2STg00:Rj2ETg00:nj2HTg00;Ij2UTg00;oj2WTg00<Uj2]Tg00=6j2MTg00=Pj2\Tg00>8j3[Tg00>\j1hTg00?:j2gTg00?[j19Tg00@:j2ZTg00@ck204Tg00ALk303Tg00B5j2eTg00Baj2dTg00CMk102Tg00Cmj3cTg00DMj1~Tg00Dmj2ITg00EKj4VTg00Eij1|Tg00FGj1zTg00G2j2bTg00GUj3aTg00H8j6wTg00H\j1vTg00I>j3GTg00Iaj3PTg00JDj4DTg00Joj2^Tg00KRj3sTg00L5j2rTg00LWj2qTg00MCj3XTg00M]j3pTg00N<j4uTg00Nnj2`Tg00OKj1oTg00Phj6TTg00QFj1nTg00Rcj2mTg00SIj2yTg00T8j3lTg00USj3{Tg00V<j3YTg00Vej7kTg00WIk800Tg00Wmk701Tf0R0#3#3p=fg00XQR1f1R2;X0p=2f2R3/02/`0p=7g00XoR49X10p=K1E431:20'Hp=81132/00p=j1E40p=C1Z10p=6A{120p==AY120p=LAY1209Y13p=?%30#3#3#3p=>P1P2g00YMP0CDp=BP2g00Z4R5g00ZSR6P6g00[3R7P0g00[SFkp=51^10p=<f3R8P5P6P6P7P3P2P0L00p=;P3P5P6P6P7P2P0K01p=_g00\3R9#3R:#3R;#3#fR<#3R=#QR>#iR?&050R@P1%Q<RA1J>0RB'xRC,t>RD%F:RE%F<R<'ORF,001J>2/0FRG'2X>1RHP110CF120GX>1P1%@9RG#@RI#@#@RJ#FRK,OERL,1B?7FLPHPBP1110L?7FL/NF%KFRH#}RM112L?7FLRN14NF,AF10NF'1'2[1RNF1:4FRN113L?7FLRO/0FRP?8PF[1SOF1:F4RO118L?7FLRP/0FRQ,:F1EQ4'H[1UPFf4RP/1L?7FLRQ/4F#K\H1WQFf5RQ/1LRR?7FLRS/0F/2S\H14SFP1f6RS/1L?7FL/0FP1f7RT/NFf8RU14UF,AF10UF'1'2\M1RUFf9RV/0FRW?8WF\N1SVFf:RV/0FRW,:F1EW4'H\O1UVFf;RW/4F#K\H1WWFf<RX/0F/2X\H14XFP1f=RX/0FP1f>/1L/NFf?/1LRY14YF,AF10YF'1'2\M1RYFf@RY/1LRM/0FRZ?8ZF\N1SMFfARM/1LRZ/0FR[,:F1E[4'H\O1UZFfBRZ/1LRO/4F#K\H1WOFfC/1LRO/0F/2O\H14OFP1fD?jLFP1PQg00\XRO1]4F'MPNeR[O1A800FPXP[O1A8UUFfEP[O1A8YYF1\E<1:4ER[%C<PN[RN[%CERXg00]>R\A[E<2UW0%CF\\^0X1\EK%CK1:4L[R<\[A[EK2V\X0X%CL\\^0XP21]4E,MOP[eR[O1P<PPP[O1PNg00]ZRN%h9,g1R[g00^FR<#9RO#9RX#9R\#9RK#9R]#9R^#9R_#6R`'=%6KRK%6ORO,=[1Z1<R<'L3?%f=#>#>#>#>#>#>#F-041>031<Ra%9_#6R_%6]R],=[%6\%6XRX'L5?`3?g00^eR\'e'd1=[K1LO<5?`1=[_%6^1=[X,LK7?]5?a/e\'d&02N5cN3c%~NP1P11I1PP31I1SCVP2P11I1QP81I1TCVCV%|1%z1RNPNPNP5P6P6P71b1ER5=a1ARA1b14R\'B,5NEwRa%v6R6%@:#<R]%QJ9a15R55G1%<I9P1A%<GRI5G1'B,5NC;P6PNP1P\g00_QRJ%<:R:CD,5NP1P:g00`8RKPACD,5N5_NP6PNPNPaP6%3G#<9P1A=G1:,B],5NC;P6PNP1P\PJ1^19R9CD,5NP1P9PKPACD,5N5_NP6PNPNPaP6As1I5%<;9P1A=G19'B,5NC;P61B9:,5NC;C;C;C;C;1rN7P0P3g00`_RNg00a?R7'M1q03=XN7dAp142CubLbObPX61X71X81X91X:1X;1X<1g00a_\HRH1AFT/18,2R[A833F1AFUR3/1P,2T\HA888F1`TL113Q'2\H12QS[[[[[^61^71^81^91^:1^;1^<1P0PWPZfOfIPVPMfHPYPUfGPTfNO<bKb5b4bMb4bNb5b1b3b2bVbSbCbBbAb2bJbUbRbIbHbGb3bFbTbQbEbDb@b1b?bWPC%oBET%F=,OE,0C/0F%nCET10DF10BFRB'2e1m>C,J>1y>CET1J>@/0F/2Be7l0X=?P0O1W=o"). Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
