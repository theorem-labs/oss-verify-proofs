(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (STACK_SPAN as the guaranteed stack span; the recorded (KReplay) proofs of ret_tail_cpsE and diag_tail_cpsE re-proved by tactics, after leptonica/colorfill_fuzzer's copy at this binary's addresses). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA Image.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_frmkit D_iface D_defs D_kit D_libiface D_clx D_rlkit D_hdr D_trdefs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_D_file3 () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC47Corelib5Lists7ListDef3mapI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list02c69OSSVerify5KrLib2K53A027D_file37s_shortC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Canon=msg_short_hdrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A027D_file36s_overC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Canon?msg_cfg_overrunC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K53A026ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs7S_SHORTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs6S_OVERC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53Lib5Image@ro_bytes_b_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem;ro_bytes_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00c69OSSVerify5KrLib2K53A027D_file3;s_short_lenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A027D_file3:s_short_roC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A027D_file3:s_over_lenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A027D_file39s_over_roC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface3rtsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A027D_file34FCTXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init5Peano2ltC69OSSVerify5KrLib2K53A028RT_iface8so_linesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2or00C69OSSVerify5KrLib2K53A028RT_iface4PMfdC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53A028RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs4EXITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs3CLXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs:main_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53A028RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53A028RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface>PMfd_fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs?PMfd_mat_stableC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53A028RT_iface7call_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC69OSSVerify5KrLib2K53A028RT_iface9unwind_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio6so_bufC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9free_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6ret_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7rt_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9rt_creditC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs;ASTA_unpackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface:rt_after_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_clx;CLX_pres_nwC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC69OSSVerify5KrLib2K53A025D_kit=agree_of_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kitArw_cells_agree_nwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_hdr=main_ret_walkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs8asta_evtC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53A025D_clx:CLX_io_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS<cps_realizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS4cpsEC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K54Spec5Canon3evwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib2K53A028RT_iface;live_removeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib2K53A028RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2K53A028RT_iface9ALLOC_RASC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027D_iface9SSP_GUARDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs7ERRNO_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026Layout<g_read_stageC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2K53A027D_iface6e_exitC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K54Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53A026D_defs4fds0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs4TP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6e_freeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8RT_STACKC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison02K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53A026D_defs7MAIN_RAC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib5Lists4List9app_nil_rC69OSSVerify5KrLib2K53A028RT_iface9rng_classC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7fs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8rt_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_clx6CLX_ioC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9in_rangesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs8drv_cellC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib2K53A025D_clxCclient_static_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_clxIoutside_of_not_in_ranges'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027D_rlkitCagree_stack_pres_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_hdr>diag_free_walkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit9agree_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027D_rlkit@main_frame_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A027D_file3=ret_tail_cpsEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:t_emit_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K52AS8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface:rt_pres_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8e_fwriteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface;STDERR_FILEC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib2K53A02:D_libiface6LIB_FPC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition s_short : list byte := map (Z_to_bv 8) msg_short_hdr.
Definition s_over : list byte := map (Z_to_bv 8) msg_cfg_overrun.

Lemma s_short_len : Z.of_nat (length s_short) = 31.
Proof.
ltac2:(KReplay.run1 (kr_t_D_file3 ()) [] "p;1p;2g0000j10Tg000Uj12Tg0013j21Tg001Mg001k#0#0#0#0#2'1o"). Qed.
Lemma s_over_len : Z.of_nat (length s_over) = 31.
Proof.
ltac2:(KReplay.run1 (kr_t_D_file3 ()) [] "p;1p;2g0000j10Tg000Uj12Tg0013j21Tg001Mg001k#0#0#0#0#2'1o"). Qed.
Lemma s_short_msg : map bv_unsigned s_short = msg_short_hdr.
Proof.
ltac2:(KReplay.run1 (kr_t_D_file3 ()) [] "p;1p;2p;4p;3p1002Pp4p710R0p1002mp4p710R1p8p1003Kp4p70R2p10049p4p710R3p8P2P0p8P2p1004Up4p710p8p10052p4p7210R2P3p8P2P1p8g005^j1?Tg0000j11Tg006>j10Tg000Uj13Tg006cj1<Tg0013j2;Tg007Cj18Tg007aj19Tg008Dj1:Tg008nj4>Tg009Jj3=Tg009dj32Tf0R1#0#3p=4g001MR2f1R3#3;21p=6f2R0A2231522p=7f4f3A22319220522522p=5%?2R0g001kR3#1R1#0R4#0R5#0R6#1#1%14R4#1R7#0#0%04#0R4#1#3R8%11#0R1#1#0R9#3%03R3#0#0R:#0#4R;P8%17R7#4R8%01R1#0#4%19%49R9%11R1#1%44R4%17#3%41R1P9%15#0R5#1#3R7P1P;P9P4%06#1#3R6P8P;P4P7P6%45%13#0%<2'69771D5D5D5D5'677;'637D5'6'6';%8:R:#9P2%::g00:DC>g00;?5=0do"). Qed.
Lemma s_over_msg : map bv_unsigned s_over = msg_cfg_overrun.
Proof.
ltac2:(KReplay.run1 (kr_t_D_file3 ()) [] "p;1p;2p;4p;3g005^j1@Tg0000j11Tg006>j10Tg000Uj16Tg006cj1<Tg0013j2;Tg007Cj1:Tg007aj19Tg008Dj1?Tg008nj4>Tg009Jj3=Tg009dj33Tf0R0#1#6p=2%00#6p=4g001MR1f1R2#6;30p=7f2R3A3120531p=8f4f3A31209313531531p=5%@1R3g001kR2#1R0#0R4#0R5#0#1#2R6%14R4#1R7#0#4R8%04#0#2R4%10#0R0#1R9#0R:#6%02R2#0#0R;#0#4R<P6%17R7#2R6%47R7%15R5#1R=#0%2=%12R2#1#1#1#1P8%05#2R5P7P<P6%19#4P5%00R0#1R5#4R9P9%2:R9P7%25P<P4P7%00#4%4:%02%<1'7589D5D5D5D5'7584'7D5D5';%:;R;#9P1%?;g00<?C>g00=95=3do"). Qed.

Lemma s_short_ro : ro_bytes_b asegs S_SHORT s_short = true.
Proof.
ltac2:(KReplay.run1 (kr_t_D_file3 ()) [] "p;2p;3g0013j22Tg00>;j31Tg009Jj30Tg00?7R0g00?WR1'2g00@7g00@og00:D31=001do"). Qed.
Lemma s_over_ro : ro_bytes_b asegs S_OVER s_over = true.
Proof.
ltac2:(KReplay.run1 (kr_t_D_file3 ()) [] "p;2p;3g0013j22Tg00>;j31Tg009Jj30Tg00?7R0g00?WR1'2g00@7g00Aig00<?31=001do"). Qed.

Lemma s_short_at : forall m, mem_inv asegs m -> bytes_at asegs m S_SHORT s_short.
Proof.
ltac2:(KReplay.run1 (kr_t_D_file3 ()) [] "h02Hah17__arithh24__ffh36__sat1h48__varmaph55__with62MIh76__sat0h81mh91zp;1p;2p;4p;3p;6p;8p;7g006>j12Tg007Cj18Tg007aj17Tg00Bbj1TTg00CDj2STg006cj1LTg005^j1CTg00D;j1ATg00DYj1@Tg00E7j1?Tg00Ebj24Tg0000j10Tg000Uj15Tg00FEj4<Tg00G0j2RTg0013j2:Tg00GRj2QTg009Jj3KTg00H>j3FTg00H]j4DTg00IOj21Tg00Ikj26Tg00JHj2BTg00Jej2ETg00KMj29Tg00Kij3GTg00LMj2HTg00Lnj3ITg00MQj3JTg00N4j2>Tg00NTj1MTg002mj6NTg00O4j4=Tg00P6j8OTg00Q1j7PTf0R0#2#2p=3f1R1g00QUg00R4R2P2g00RTR2P0g00S4FPp=;g001kR3#2R4#3R5#2#3R6#8R7#7%85#7R8#T[g00@7R9/S0P9P1g00@oR:g00:DR;P0g00STR<#LR=%C<R<g001MR>#AR?%@>R@%?>RAP>g00T@RB,4>g00T^RC%05#2#0#0#3#3#0#2#3#0#0#5R5,4>RDC<';1RA2R2P0f2REg00?7RFg00?WRG':1Q0E=KFGdAF>B1CDRGb2b4b511B5P0b111B:eP>%03#0#0#0#5R316:0%54R4%56R6'BRF'1X9>1E4619B4RE11B619BF[RH[11B4RIg00UERJAG461UW011BF\J^0IP1g00Ua1HB4':PEeO1PHP=P<P?P@P>14>39I>DPC14>4=J>7C<,;AP2PGb2b4b51653/1FP0b1b3b7b316:3/1Fe1>8;#Mg00VGENP9P;P:g00WFC=GOW6W8o"). Qed.
Lemma s_over_at : forall m, mem_inv asegs m -> bytes_at asegs m S_OVER s_over.
Proof.
ltac2:(KReplay.run1 (kr_t_D_file3 ()) [] "h02Hah17__arithh24__ffh36__sat1h48__varmaph55__with62MIh76__sat0h81mh91zp;1p;2p;4p;3p;6p;8p;7g006>j13Tg007Cj18Tg007aj17Tg00Bbj1TTg00CDj2STg006cj1LTg005^j1CTg00D;j1ATg00DYj1@Tg00E7j1?Tg00Ebj24Tg0000j10Tg000Uj15Tg00FEj4<Tg00G0j2RTg0013j2:Tg00GRj2QTg009Jj3KTg00H>j3FTg00H]j4DTg00IOj21Tg00Ikj26Tg00JHj2BTg00Jej2ETg00KMj29Tg00Kij3GTg00LMj2HTg00Lnj3ITg00MQj3JTg00N4j2>Tg00NTj1MTg002mj6NTg00O4j4=Tg00P6j8OTg00Q1j7PTf0R0#3#3p=2f1R1g00QUg00R4R2P2g00RTR2P0g00S4FPp=;g001kR3#3R4#2R5#3#2R6#8R7#7%85#7R5#T[g00@7R8/S0P8P1g00AiR9g00<?R:P0g00STR;#LR<%C;R;g001MR=#AR>%@=R?%?=R@P=g00T@RA,4=g00T^RB%04#0#2#0#0#0#3#2#2#0#2#5RC,4=RDC<';1R@2R2P0f2REg00?7RFg00?WRG':1Q0E=KFGdAF=A1CDRGb2b4b511ACP0b111A9eP=%03#0#0#0#5R31690%54R4%56R6'BRF'1X9=1E4619A4RE11A619AF[RH[11A4RIg00UERJAG461UW011AF\J^0IP1g00Ua1HA4':PEeO1PHP<P;P>P?P=14=39I=DPB14=4=J=7C<,;@P2PGb2b4b516C3/1FP0b1b3b7b31693/1Fe1>5:#Mg00XDENP8P:P9g00YBC=GOW6W8o"). Qed.

Section File3.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis FRE : free_contract RT.
Hypothesis FWR : fwrite_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, CREDIT_DRV, g_read_stage in *; lia.

(* [comment removed for export] *)
Definition FCTX (Σ : rts RT) (so : stdout_st) (usp buf cap : Z) (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ CLX OUT_rep ERR_rep XENV LIB so m /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7
  /\ stk asegs m (rt_sp0 RT Σ - STACK_SPAN) (usp - 80)
  /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_SPAN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
  /\ rt_live RT Σ = [(buf, cap)] /\ rt_frames RT Σ = [] /\ usp + 16 <= USTACK_TOP.

(* [comment removed for export] *)
Theorem ret_tail_cpsE : forall (Σ : rts RT) (so : stdout_st) (code usp buf cap : Z)
    (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  FCTX Σ so usp buf cap c0 c1 c2 c3 c4 c5 c6 c7 m -> 0 <= code < 256 ->
  (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
  cpsE asegs (ASTA RT Σ (PMfd fds0 fs)
               (eq (entry_st (Z_to_bv 64 0x960b8) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 code)
                     (Z_to_bv 64 buf) (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m)))
    (evw 1 (so_buf so)) (EXIT fs code).
Proof using AF AF_DRV FRE EXC OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros Σ so code usp buf cap gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7
    F fc m HF Hcode Hso T c HA Hk.
  destruct HF as (ART0 & MI0 & CLX0 & FR0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (lo := rt_sp0 RT Σ - STACK_SPAN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  apply (FRE Σ (PMfd fds0 fs) (Z_to_bv 64 0x960b8) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 code)
           (Z_to_bv 64 buf) (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf cap lo);
    try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - rewrite LV. left. reflexivity.
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - unfold unwind_ok. rewrite EU, !unsigned_lit by ul. split; [cbn; tauto|]. left. ul.
  - intros cf1 (Σ1 & v & Hc1 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PRES1) & Hc1').
    destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    rewrite EU in ST1, PRES1.
    rewrite (ret_pc_even 0x960b8) in Hc1' by lia.
    assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB so m1)
      by exact (CLX_pres_nw OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img _ m m1 _ _ _ CLX0 PRES1).
    pose proof CLX1 as (OUT1 & ERR1 & XE1 & _).
    destruct FR0 as (junk & FR0).
    assert (FR1 : rw_cells asegs m1 (usp - 80) [CB 8 junk; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 (Z_to_bv 64 MAIN_RA)]).
    { apply (rw_cells_agree_nw asegs m m1 _ _ FR0). apply (agree_of_pres _ _ _ _ _ _ PRES1).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (main_ret_walk usp gp (Z_to_bv 64 code) (Z_to_bv 64 buf) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v u0 u1 u2 b1 b2 b3 b4 b5 b6
                  b7 u3 u4 u5 u6 F1 fc1 m1 lo c0 c1 c2 c3 c4 c5 c6 c7 junk ST1 ltac:(ul) ltac:(ul) B16 ltac:(ul) FR1 MI1) as W1.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (-> & ST2) & Hc2').
    apply (EXC Σ1 fds0 fs (Z_to_bv 64 0xe9ba0) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) u0 u1 u2 c0 c1 (Z_to_bv 64 code) b1 b2 b3
             b4 b5 b6 b7 c2 c3 c4 c5 c6 c7 s8 s9 s10 s11 u3 u4 u5 u6 F1 fc1 m1 so code lo); try reflexivity; try assumption.
    + unfold call_ok. rewrite unsigned_lit by ul. rewrite SP1. split; [exact ST2|]. ul.
    + io_ssp_tac AF_DRV.
Qed.

(* [comment removed for export] *)
Theorem diag_tail_cpsE : forall (Σ : rts RT) (usp buf cap sa : Z) (s : list byte)
    (gp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  FCTX Σ stdout_init usp buf cap c0 c1 c2 c3 c4 c5 c6 c7 m ->
  bytes_at asegs m sa s -> acc asegs m sa (Z.of_nat (length s)) -> 0x10000 <= sa -> sa + Z.of_nat (length s) <= SEGTOP_A ->
  0 < Z.of_nat (length s) <= 64 -> (sa = 0x22c23 \/ sa = 0x16704) ->
  cpsE asegs (ASTA RT Σ (PMfd fds0 fs)
               (eq (entry_st (Z_to_bv 64 0x960b0) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2)
                     (Z_to_bv 64 buf) (Z_to_bv 64 sa) (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 1) (Z_to_bv 64 STDERR_FILE)
                     a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fwrite m)))
    (evw 2 (map bv_unsigned s)) (EXIT fs 2).
Proof using AF AF_DRV FRE FWR EXC OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros Σ usp buf cap sa s gp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 F fc m
    HF HB HAC H1 H2 H3 HSA.
  pose proof HF as (ART0 & MI0 & CLX0 & FR0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & UT0).
  pose proof CLX0 as (_ & ERR0 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (lo := rt_sp0 RT Σ - STACK_SPAN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  intros T c HA Hk.
  replace (evw 2 (map bv_unsigned s)) with (evw 2 (map bv_unsigned s) ++ evw 1 (so_buf stdout_init))
    by (cbn [so_buf stdout_init evw map]; rewrite app_nil_r; reflexivity).
  eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
  apply (FWR Σ fds0 fs (Z_to_bv 64 0x960b0) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
           (Z_to_bv 64 sa) (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 1) (Z_to_bv 64 STDERR_FILE) a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sa s STDERR_FILE lo); try reflexivity; try assumption.
  - split; [intros _; split; [exact HAC| right; right; right; ul]| left; ul].
  - io_ssp_tac AF_DRV.
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - intros cf1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (v & m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & ERR1 & OUTP1) & Hc1').
    destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    rewrite EU in ST1, PRES1.
    rewrite (ret_pc_even 0x960b0) in Hc1' by lia.
    pose proof CLX0 as (OUT0 & _).
    assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB stdout_init m1)
      by exact (CLX_io OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                  _ _ m m1 _ _ _ CLX0 PRES1 WM1 (OUTP1 _ OUT0) ERR1).
    pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES1 ltac:(intros x Hx; apply outside_of_not_in_ranges'; intros Hin;
                  pose proof (client_static_range _ (proj1 (IO_img _ Hin))); ul)) as AG1.
    pose proof (diag_free_walk usp gp u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 2) (Z_to_bv 64 buf) s2 s3 s4 s5 s6 s7
                  s8 s9 s10 s11 u3 u4 u5 u6 F1 fc1 m1 MI1) as W1.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
    apply (ret_tail_cpsE Σ stdout_init 2 usp buf cap gp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
             c0 c1 c2 c3 c4 c5 c6 c7 F1 fc1 m1); [| lia| left; reflexivity| exact Hc2'| exact Hk].
    split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
    split; [apply (main_frame_agree m m1 usp _ _ _ _ _ _ _ _ FR0); [eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; ul| exact WM1]|].
    split; [exact ST1|]. tauto.
Qed.

End File3.
