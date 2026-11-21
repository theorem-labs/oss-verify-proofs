(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (STACK_SPAN as the guaranteed stack span; the recorded (KReplay) proof of seg_read re-proved by tactics, after leptonica/colorfill_fuzzer's copy at this binary's addresses). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_frmkit D_iface D_defs D_kit D_libiface D_clx D_usage D_open D_read D_rlkit D_loopdefs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_D_loop1 () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC4ELinuxProcessSemantics?LinuxProcessSem2FsCfile_read_unguardedK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init3Nat3subC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=length_firstnC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01C35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53B026D_defs6path_bC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC69OSSVerify5KrLib2K53Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_rlkit?fd_insert_twiceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_loopdefs2FDC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C69OSSVerify5KrLib2K53B026D_defs4fds0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_loopdefs2RLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_loopdefs5RDONEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_loopdefs4RMEMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface3rtsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53B02:D_loopdefs4DCTXC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53B02:D_loopdefs5LOOPSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_loopdefs6cap_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs7MAINCTXC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K53B028RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs8argv_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs:main_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib2K53B028RT_iface9rt_creditC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_loopdefs<cap_ok_rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK47Corelib4Init5Logic2or01C69OSSVerify5KrLib2K53B028RT_iface=af_live_rangeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_rlkitAchecked_dst_stageC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53B028RT_iface7call_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC69OSSVerify5KrLib2K53B028RT_iface6ret_stC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B027D_loop1@file_read_firstnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B027D_loop1Clength_firstn_skipnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs;ASTA_unpackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8rt_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B027D_loop17FD_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_clx8CLX_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_rlkitCagree_stack_pres_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_loopdefs:DCTX_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53B025D_kit@agree_of_pres_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_kit>bytes_at_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib2K53B028RT_iface4PMfdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_read8eof_walkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs8asta_evtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith4Znat5Nat2Z2idC46Stdlib5Lists4List:firstn_allK47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53Lib5RzCPS<cps_realizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_read<read_ok_walkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B027D_loop1Afirstn_len_firstnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs3CLXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K53B028RT_iface:rt_pres_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface6e_readC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib2K54Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs:CREDIT_DRVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_iface9SSP_GUARDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs7ERRNO_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026Layout<g_read_stageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_iface7e_closeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8e_memcpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53B026D_defs4TP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison02C69OSSVerify5KrLib2K53B028RT_iface8RT_STACKC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00C46Stdlib9micromega8ZifyInst7Inj_Z_Z".
Import ListNotations.
Open Scope Z_scope.

Lemma file_read_firstn : forall data len count, 0 <= len < 2^64 -> 0 <= count < 2^64 ->
  file_read data (Z_to_bv 64 len) (Z_to_bv 64 count) = firstn (Z.to_nat count) (skipn (Z.to_nat len) data).
Proof.
ltac2:(KReplay.run1 (kr_t_D_loop1 ()) [] "h06__sat4h12Hah27__arithh36__sat3h44__x1h51zh62H1h72H2h84__ffh98__varmaph:5__with;5counth<4datah=1lh>3lenp;1p;2p;3p;4p;7p;8p;6p10000p4p70R0p1000`p4p710R1p8P0g001<R0p4p710R2p8p1001Zp4p7210R3P1p8P3P2p8p1002Fp4p710P1p8g002ej10Tg003Jj1CTg003hj1NTg004Kj1BTg004kj24Tg005Gj1ATg005ej2UTg006Bj26Tg006^j2=Tg0079j27Tg007_j1?Tg008Zj33Tg0098j32Tg009Wj11Tg00:7j35Tg00:Qj2:Tg00;;j28Tg00;Uj2WTg00<=j3VTg00<aj2TTg00=Bj1RTg00=bj2QTg00>@j1MTg00>^j1LTg00?Ij2>Tg00?lj2ITg00@Oj4<Tg00A:j3HTg00A]j7JTg00BAj1KTg00Bcj8GTg00CGj2FTg00Cij2OTg00DUj3ETg00E4j4PTg00Efj2@TP0j69Tg00Fej3DTg00GZj3STg00HYj7XTf1R0g00I=R1g00I\R2P2g00J<R3f0R4g00J\FXp=;g00K<R5#0R6#0#0R7#C#NR8#BR9g00KaR:g00L?R;/40%A6R6%07#0#0R7#AR<'UR=,60'=R>P9%C7R7f2R?'7R@#?f3RA,77RB#?f4RC538528RD%1ARE%1Cf5RF538528RG9594X=9P:P?%14RH177C,:7#1=38F528=59GX5:P:PAA38HF928E=59GX5:%1?A38EC528R8,891:7B1W6<RE16;6RG14;<16;=[RH[RI14;6RJg00L]RKAV6<0UW1R<14;=\K^1JRJP0g00M91T;6'8PGeO1RGPHg00M_RK#R%BK1Q:0%M:%L:RKP1P2P2P3PKP1P2P2P3P:1>:;g00NK1I:5R5C<,;KP:P5g00O21>:6=H:7C<,;KFJR6%K2P6GG1FK3P4P?g00OYRKg00P9R3'81O4?=5K3dAE:;0CPb8b9b:X4:R014;4164='=P>[^4:R=P4f7PFO2b2b0b3b0,@AE91:7@PEPIP<PJPGPHP0P=P4f6PCO2b2b0b3b0,@?E9A59D8eADCB@ASCB@E9X7>W6X;:W>W<o"). Qed.

Lemma length_firstn_skipn : forall {X} (l : list X) len count, 0 <= len <= Z.of_nat (length l) -> 0 <= count ->
  Z.of_nat (length (firstn (Z.to_nat count) (skipn (Z.to_nat len) l))) = Z.min count (Z.of_nat (length l) - len).
Proof.
ltac2:(KReplay.run1 (kr_t_D_loop1 ()) [] "h01xh11nh24__p1h34__x1h44__x2h54__x3h64__x4h74__x5h84__x6h94__x7h:4__x8h;2H1h<2H2h=2H3h>2H4h?2H5h@2H6hA2H7hB1XhC7__arithhD4__ffhE8__varmaphF5__withG5counthH4cstrhI1lhJ3lenhK1mhL1yhM2z3hN2z4hO2z5hP2z6hQ2z7p&0p;1p;2p;3p;<p;4p;6p;Bp;7p;8p200R0g008ZR1p4p710p8P0g00PYR2p4p710p8P0g00Q9R3p4p710p8g004Kj1hTg004kj2@TP2j2;Tg00QZR2j19Tg006^j2NTg009WR4j1eTP1k303Tg00R:j2YTg00RQj2=Tg00RnR1j2HTg00SKj2kTg00:7k10<j3PTg00Sbk10;Tg00;;j2ITg00T@l<~Tg00Tej1{Tg00UJj2_Tg006Bj2LTg00Ulj2XTg00VNj12Tg00Vmj1mTg00WKj2lTg00Wlj2\Tg00=Bj1jTg00=bj2TTg00XUk10:Tg00Y3j4STg00>@k109Tg00>^k108Tg002ej1RTg00YQj1ZTg00?lj2dTg00BAk104Tg00?Ik201Tg00Z6j3cTg00ZYk600Tg00CGj2wTg00Cij2vTg00DUj3uTg00E4j4tTg00[=j4sTP3j3xTg001<j6`Tg0098j3rTg00[hj3qTg00\Jj2pTg00\gl<]Tg00]LlBaTg00^2j2bTg00^Lj3oTg00_5j3CTg00_^j2ETg00`Jj3:Tg00@Oj4KTg00HYj7GTg00A]j7WTg00`jj7nTg00Bck807Tg00KaR3f1R5f0R63Pp=5g00L?R7/p6p=6P3g00aNR8P3P3P4f4R4P2f3R9g00amf2R:P5P6M<]p=fP8P8P8P3P3P3g00bZP2P2P2f6R;g00c:f5R<P4P9P:P5P6MBap>06P8P8P8P3P3P3g00caP2P2P2P1g00dAP<P4P9P:P5P6MBap>05P8P3P3P3P2P2P<P4P9P:P5P6M<]p>02AP349,N<1@:5/N6'bp=>1L76p=DAP367p=O1\36p=4Ao356p=?AC3569C3:p=0AC356g00ddR2'Ep=7AC3569C3:/E2p=3AC356p=1g00M_R1A:1567::p=UA:1569:1:9:199:14p=81E52=:16p=iAC3:5/E2=:16p=F1E:21E52=:165:1p=[1d36p=BP3P5g00O2P6CKp=QP<g00I=R2g00I\R=P=g00J<R>P4P2P=P=P>P9g00J\R?FGP:P2P=P=P>P3P5g00ePR@P6CKP?FGFWp=<P3P5g00NKRAP6CKp=JP:P2P=P=P>P5P6Fnp=MP3P5P@P6CKp=}P9P2P=P=P>P:P5P2P=P=P>P6P?FGFWp=|P:P2P=P=P>P3P5PAP6CKP?FGp=VP9P2P=P=P>P:P2P=P=P>P5P?FGP6FWp=zP:P2P=P=P>P3P5P@P6CKP?FGp=yP9P2P=P=P>P:P5P6L07p=A1@:5/N6p=^1N:5/b6p=g%h61@75R?1;9:#9,@5'NP8%e:R@%e9RA>03<4RB,;<RC'Y%96RD1;;<#9/=4RE,H9RF'5X18P81;<4RG/kARH1YA6#9/5FX181Y@HRI#9RJ%9GRK/=9,H:RL'5%6:RM%69RN,=K#6RO'HRP/5LP3P3&0<3RQP6X03RRPQ1556$0;XL3X03PJPPPRPR1I3DX08PIPPP@PMPR%66X03RMP:P:1I3:DfPHPO1=56#6XK3X13PGPK1I3KPAPNPRPMP9P91I39DfK06J05J02PLPL1I3LM<~%{G1@7K1_9E1L9EPFP9PEP915FEE>f7RF/;;#9/=<,H4P31X7;%D;%6;REP;P;P7%OEE>%6FP3f:REf9RK';#9/=6RG,X7%DG%6GRLPGPGP7%OLE>f;RL/;E#9/=5#6P31X7K%DK%6KRGPKPKP7%OGE>%6EP31_6:1L6:1H6:RGP6P:P615G:E>1H59P3p-0RGg00f7RM#2RR#2RN#2RO#2RH#2RP#2RI#2R8#2RD#2RJ#2RQ#2RS#2RT#2RU#4RV%4JRJ%4DRDg00K<RW#m,l3RX%4PRP'?RY%4H1\3MRM3030'7RH1?XVRZ%4QRQ1?XJR[%48R8%4NRN=0PMR\30R]33R^%4IRI/1\90[8R\93ZQR_%4O=0YMRO93VJR`%4TRT?3DORa1?XTRb1?XDRc11PMRP,1IRd708Re73JRfA0c8PRg93bJRh%4R/1M90DY,7TRR%4SRS1?X8Ri/1IRj73JRkPk17beReA0QJc,7V%2U#4RUA0SQ['7R[P[P[P[11YMRM90DiRi90VJRY11Z]A0VSMR]A0TQMRM17bg11TiRiPRPhPfPaP`P_P^PH1?XSRH/1JR^93UTR_P_11IN90Q8,7TRNPNA0J8I,7SRIPI1?XQRX/1DRI93VSR8P811Dj90VX11XPRj,1b11HPRP11HdRH17UYRYPYA3ZTHRHA3ZTPRPA3VSORYA3TQORTA3bSjRjPk17VI11Xd90bSPjPTPYPP17U^%j15UHD8'i5UkD8D85FZ5FZ9[M]3[9FViD8D8D8D8'i5Ue5FV5FU9FZ\3[D8D8D8D8%h1P3P3P3f8R1,T3P4&0:3CSP:1T3;CSP5P31T3<P91T3FCSCS&093&083R\P\P\%RWRZ#RRU#R#BRV%ZWRe#Z#BRi'QP\1d3WRWPVE<P\P\1JiVP\PWPiE<5M\&04=RMP\P\P\20137R]%ZZ#BRk'QP\PVPkE<P\P\1Jk]P\PVP]E<5M\PMP\P\P\%BURU%Re#BRV5c3RH,Q]P\PiPHE<P\P\1JH]P\PiP]E<5M\PMP\P\P\P2P=P=P>PEJ00P\%BeRe,}VC|P\P\1Je]P\PVP]E<5M\PMP\P\P\Ac3UeRV,QkP\%BZRZPkE<P\P\1JVkP\PZPVE<5M\PMP\AV\]UPMP\AV\]kPMP\P\P\1J]eAV\eUCzPMAy\WZCACACACACACACACA1w\>P6P:g00OYR\g00P9R>'I1v6:=P\>dAu375CtbDbEbFX33X43X53X63X73X83X93X:3W21LF;P6PFP;PF156;E>%D<151<R>%O1R\9^<7RZ3g1=<FRW#DP1PWPWP7P\E>AgL>Z1=F;RZ,L1P<P1PZP115<ZE>1@711@7E1@KE9^7K151K[[[[[[[[^33^43^53^63^73^83^93^:3^2GP6f?R6#DP9P<PFf>fAf@';#9P6PKP5P:P4P;P1PEPLf<f=OAbCbQbAbPb@bOb?bNb>bMb=bHCsPCAx<A4E`Ar<@B,;<Aq<@BE`X<?W;XG3XJ3WIXB0o"). Qed.

Lemma firstn_len_firstn : forall {X} (l : list X) k, firstn (length (firstn k l)) l = firstn k l.
Proof.
ltac2:(KReplay.run1_chk (kr_t_D_loop1 ()) [] "p'0h01li001lh11kh22l0h31xi011xh42IHh51Xp;1p;3p;2p;8p;5p200R0g0098R1p4p710p8P0g00fVR2p4p710p8P0P2p4p7210p8P0p1001<p4p710p8P0g00PYR3p4p710p8g004KR4j10TP1j31Tg00:7j33Tg00=Bj16Tg00;;j24Tg00`Jj37j2;Tg00VNj15TP2j8:Tg00g3j58TP3j29Tf3R3f2R2f1R1'9f0R531p=2%05g00aNR6%03R7f4R8#0R9P8P8A1815R:P5C2;3:]0R:X16%02P4P3P8P8g00f7R;=185R8P5C2=398P5%63R8,47P3P3A13;8R<P8C2=37<ef5R<f6R7#0R8f7R=#0R>%6='4P=P=A7=15R?91=;R;P?C2=3>;eW0W3P1P5O2n10110000020020101100W2P4P<P7P7%53=175R3P5C2=383P5%0<R3%6<R8'4P<P<%52=1<8R2P8C2=332ef8#0f9R2#0R3P31;21R8P8P2P2A1275R4P5C2P4f:#0\3/48P<P5O1G:P2P2%57A7215R7512R2P7C2=332eW0X3=P1P5O2n10110000020020101100X29X4:X16P5P1D8W1W0X50o"). Qed.

Lemma FD_step : forall argvb len k, 0 <= len -> 0 <= k -> len + k < 2^64 ->
  fd_insert (FD argvb len) (Z_to_bv 64 3) (FdFile (path_b argvb) (Z_to_bv 64 len + Z_to_bv 64 k)%bv) = FD argvb (len + k).
Proof.
ltac2:(KReplay.run1 (kr_t_D_loop1 ()) [] "h02H1h12H2h22H3h35argvbh41kh51lh63lenp;1p;2p;3p;8p;4p;6g002ej10Tg003Jj1=Tg003hj1:Tg004Kj14Tg004kj2HTg00gTj25Tg005Gj16Tg005ej2BTg006Bj2@Tg00h1j2?Tg00YQj1>Tg0079j22Tg00hQj17Tg00iJj3GTg00ioj23j1ETg00jgj31j2FTg00:7j3;Tg00;;j29Tg00k_j2DTg00fVj8<Tg00l]j4ATg001<j6CTg00m`j28Tg00K<R0#0R1#0#0R2#=#:#4#4g00KaR3g00L?f1'HR4f3R5f2'5%61%02#0#0R2#6'B'@%=2R2#:R1g00nYR6'?#4R7g00oQR8%>0#6,22R0f5R9#7R:f4R;,22R<12255G2R='3R>31f0f6#7159;,22'391805;7X57P6P71F80R?P?P>15;5R@,22R2,3:P7\6/9?P1P6%E:R?P?P=P2P6\1/9?1D;5G<G<13:<R<9180?10>P8P0P<P>CAEC189;?10>189@5;7eW2X14W0X43W6W3o"). Qed.

Section Loop1.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Variable data : list byte.
Hypothesis HDATA : fs_lookup fs (path_b argvb) = Some data.
Hypothesis AF : art_facts RT.
Hypothesis RFILE : read_icontract_file RT.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.

Theorem seg_read : forall len cap,
  cps asegs (RL RT OUT_rep ERR_rep XENV LIB argvb fs data len cap)
            (fun c => RDONE RT OUT_rep ERR_rep XENV LIB argvb fs data c \/ RMEM RT OUT_rep ERR_rep XENV LIB argvb fs data len cap c).
Proof using HDATA AF RFILE OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros len cap T c HR Hk.
  destruct HR as (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
                  & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & HA & HD & HLS & HBUF & Hlen & Hld & HCAP).
  pose proof HD as ((ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0) & HB & Hap & Hhi & SPW).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof HLS as (LV & FRS & CR & USP0').
  pose proof (cap_ok_range cap HCAP) as CAPR.
  pose proof (af_live_range RT AF Σ m buf cap ART0 ltac:(rewrite LV; left; reflexivity)) as (PR1 & PR2 & PR3).
  set (lo := rt_sp0 RT Σ - STACK_SPAN) in *.
  set (count := Z.min (cap - len) 65536) in *.
  assert (CNT : 0 < count <= 65536) by lia.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  pose proof CLX0 as (_ & _ & _ & _ & _ & _ & RS0).
  apply (RFILE Σ (FD argvb len) fs (Z_to_bv 64 0x9615c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2)
           (Z_to_bv 64 buf) (Z_to_bv 64 3) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) a3 a4 a5 a6 a7 (Z_to_bv 64 path)
           (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 g_read_stage) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
           3 g_read_stage count (path_b argvb) (Z_to_bv 64 len) data lo); try reflexivity; try assumption.
  - lia.
  - ul.
  - exact (checked_dst_stage RT AF Σ m _ count ART0 RS0 ltac:(lia)).
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - intros cf1 Hc1.
    rewrite (file_read_firstn data len count) in Hc1 by ul.
    set (bs := firstn (Z.to_nat count) (skipn (Z.to_nat len) data)) in *.
    assert (LBS : Z.of_nat (length bs) = Z.min count (Z.of_nat (length data) - len)) by (apply length_firstn_skipn; lia).
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & BS1) & Hc1').
    destruct RS1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    rewrite EU in ST1, PRES1.
    rewrite (ret_pc_even 0x9615c) in Hc1' by lia.
    rewrite (FD_step argvb len (Z.of_nat (length bs))) in Hc1' by lia.
    assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB stdout_init m1)
      by exact (CLX_read OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                  _ m m1 _ _ _ bs CLX0 PRES1 WM1 BS1 ltac:(lia)).
    pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES1 ltac:(intros x Hx; cbn; split; [ul| exact I])) as AG1.
    assert (HD1 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m1)
      by exact (DCTX_agree RT OUT_rep ERR_rep XENV LIB argvb AF Σ Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m m1 HD ART1 MI1 WM1 ST1
                  eq_refl CLX1 AG1).
    assert (HBUF1 : bytes_at asegs m1 buf (firstn (Z.to_nat len) data)).
    { apply (bytes_at_agree asegs m m1 _ _ HBUF). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES1).
      intros x Hx. rewrite length_firstn in Hx. split.
      - right; right; left. exists buf, cap. rewrite LV. split; [left; reflexivity| lia].
      - cbn. split; [| exact I]. unfold g_read_stage, SEGTOP_A in *. lia. }
    destruct (Z.eq_dec (Z.of_nat (length bs)) 0) as [Z0|NZ].
    + (* [comment removed for export] *)
      assert (EL : len = Z.of_nat (length data)) by lia.
      replace (len_word bs) with (Z_to_bv 64 0) in Hc1' by (unfold len_word; rewrite Z0; reflexivity).
      pose proof (eof_walk usp gp t0' t1' t2' (Z_to_bv 64 buf) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path) (Z_to_bv 64 len)
                    (Z_to_bv 64 cap) (Z_to_bv 64 g_read_stage) s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1 MI1) as W1.
      lazymatch type of W1 with evt asegs _ ?X =>
        assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
      clear W1.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W1') Hc1').
      intros cf2 Hc2. apply Hk. left.
      destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
      exists Σ, usp, ap, path, buf, cap, gp, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', s8, s9, s10, s11, t3', t4', t5', t6'.
      exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m1.
      rewrite Z0, Z.add_0_r, EL in Hc2'.
      split; [exact Hc2'|]. split; [exact HD1|]. split; [exact HLS|].
      split; [| split; [lia| exact HCAP]].
      rewrite EL, Nat2Z.id, firstn_all in HBUF1. exact HBUF1.
    + (* [comment removed for export] *)
      pose proof (read_ok_walk usp buf len (Z.of_nat (length bs)) gp t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path)
                    (Z_to_bv 64 3) (Z_to_bv 64 cap) s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1 ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(ul) MI1) as W1.
      lazymatch type of W1 with evt asegs _ ?X =>
        assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
      clear W1.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W1') Hc1').
      intros cf2 Hc2. apply Hk. right.
      destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
      exists Σ, usp, ap, path, buf, (Z.of_nat (length bs)), gp, t0', t1', t2', a3', a4', a5', a6', a7', s8, s9, s10, s11, t3', t4', t5', t6'.
      exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m1.
      split; [exact Hc2'|]. split; [exact HD1|]. split; [exact HLS|]. split; [exact HBUF1|].
      split; [rewrite Nat2Z.id; unfold bs; rewrite firstn_len_firstn; exact BS1|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact HCAP].
Qed.

End Loop1.
