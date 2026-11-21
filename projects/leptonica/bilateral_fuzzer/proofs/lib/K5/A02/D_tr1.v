(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (STACK_SPAN as the guaranteed stack span; the recorded (KReplay) proof of tr_start re-proved by tactics). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_frmkit D_iface D_defs D_kit D_libiface D_clx D_rlkit D_trdefs D_trpro D_trwalk.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_D_tr1 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC69OSSVerify5KrLib2K53A028D_trdefs8tr_callsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2K53A028RT_iface3rtsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib2K53A025D_tr14TPREC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface4PMfdC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53A028RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs:main_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53A028RT_iface9rt_creditC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53A028RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53A028RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List2InK47Corelib4Init5Logic2or01C69OSSVerify5KrLib2K53A028RT_iface=af_live_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A025D_tr1>tr_calls_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideK47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53A027D_trpro7tr_pro1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028D_trdefs8tr_frameC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53A028RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs;ASTA_unpackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8af_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_clx9CLX_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit>agree_of_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit8agree_onC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalK69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs:drv_constsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs<stderr_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9in_rangesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs8drv_cellC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib2K53A025D_clxIoutside_of_not_in_ranges'C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53A028D_trdefs?CLX_xenv_updateC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53A025D_clxCclient_static_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit9agree_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit>bytes_at_agreeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC69OSSVerify5KrLib2K53A025D_kit;agree_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027D_rlkit@main_frame_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028D_trdefs>tr_frame_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib2K53A027D_trpro=tr_pro2_emptyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028D_trdefs4TCTXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028D_trdefs7tr_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem<bytes_at_nilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega=RingMicromega5Psatz07C46Stdlib9micromega;ZifyClasses5mkrelC69OSSVerify5KrLib2K53A027D_trpro<tr_pro2_copyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface>PMfd_fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs?PMfd_mat_stableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00C69OSSVerify5KrLib2K53A028RT_iface5mcostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9sec_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbK46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib2K53A028RT_iface7call_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC69OSSVerify5KrLib2K53A028RT_iface9unwind_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface;malloc_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6ret_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8rt_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K53A028RT_iface<af_live_disjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_clx8CLX_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027D_rlkit@agree_stack_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit=agree_of_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028D_trwalk<tr_copy_walkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface;checked_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027D_rlkit@checked_src_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface;checked_dstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027D_rlkit@checked_dst_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9icpt_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface:rt_pres_exC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_clx;CLX_pres_exC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027D_rlkitCagree_stack_pres_exC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028D_trwalk@tr_copy_ret_walkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic5proj2K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53A028D_trdefs5TLOOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs3CLXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs8asta_evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz05C69OSSVerify5KrLib2K53Lib5RzCPS<cps_realizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface7rt_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028D_trdefs<e_target_runC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib2K54Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs:CREDIT_DRVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib2K53A026D_defs4fds0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib2K53A027D_iface9SSP_GUARDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs7ERRNO_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026Layout<g_read_stageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027D_iface7GOT_SSPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs<GOT_LLVMINITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs7S_SHORTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs6S_OVERC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2K53A02:D_libiface9FUZZ_COSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs8TR_EMPTYC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib2K53A028RT_iface8e_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9ALLOC_RASC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8e_memcpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53A026D_defs4TP_AC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53A026D_defs7TR_INITC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:D_libiface6LIB_FPC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison02C46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib2K53A028D_trdefs5TR_M2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8LIVE_MAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9SEC_BYTESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8RT_STACKC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02".
Import ListNotations.
Open Scope Z_scope.

Lemma tr_calls_range : forall L c0, 1 <= tr_calls L c0 <= 4.
Proof.
ltac2:(KReplay.run1 (kr_t_D_tr1 ()) [] "p'0h07__arithh14__ffh28__varmaph35__with46__sat2h52Hah66__sat1h76__sat3h84__x1h91Hh:1Lh;1bi001bh<2c0h=1zp;1p;2p;3p;4p;8p;6p;7p10000p4p7210R0p1000\p4p710p8P0g0018R0p4p710p8g001Vj1<Tg002;j1@Tg002Yj1KTg003<j2DTg003Yj16Tg0047j25Tg004aj1OTg005Fj2>Tg005dj2;Tg006Aj20Tg006]j22Tg0078j1BTg007Xj1ATg0088j1_Tg008Vj1VTg0094j1UTg009_j27Tg00:Bj2NTg00:dj2?Tg00;>j2JTg00;jj3ITg00<Dj3HTg00<cj4FTg00=Uj2GTg00>2j2:Tg00>Rj2ETg00?:j28Tg00?Vj3CTg00@:j2LTg00@[j3MTg00A>j4=Tg00Aij3PTg00BPj2QTg00CAj2RTg00C_j2STg00DBj1TTg00Ddj3^Tg00EGj8]Tg00Ekj1\Tg00FIj3WTP0j6XTg00Flj2YTg00Gij7ZTg00HMj7[Tg00I1R0f1R1g00IOf0R2C=p=4P1g00J6R3g00JUR4P4g00K5R5P2g00KUFZp=1f2R6P3P4P4P5P1P2F[p=9g00L5R7/02p=3g00LSR8#<R9#<R:#<#@R;#K1D17g00M8R<P<%68R=P<P0P2P=15;6%O8#6'>/;=n0100000020000R>'0%6:R:,0>'2P2g00MXR>#BR?%A>R>%_0R@%V0RA%U0RB170=RC/4C,1B170:RD,4C,1B391NB5REP2P6g00NDRF,?<1J26=I<FdAH071CFRFb1b2b310==10=:'2P2b0P015;1R<%69RG/GGRH':RI1;2=RJ,0=10J:'2X=01EGGRJ187GRK%3GRL187HRM[RN[ROg00NdRPACGG1UX5LRQ%3HRR\P^5LRPP1g00O@1L7G'?PKeRKO1PNP?P>P@PAP01707R7g00OfRS170GRT%@95M0R9C=,1BPEPFb1b2b3PMP2b0b4b6b49P<H%3I18IH'2PJPOPQPPf4,5;RP/QH%3Pf6,5;/:H#3\R[P6PKO1PNP?P>1R01PAPBP3P4P4P51S08R8,47,1BP0P8PSP9C=,1B59B%T4A^08CR8,4C,1B148D,1B59BG]PEPFb1b2b3X80%32182H'21;1=R8,0=108:'2[^80P2f7,5;/:Hf5O2b0b7b6b4b7b9%\G,><P?P>P@PA147T,1BPEPFb1b2b3PLP2b09W<GEXn0110000020001b;1Y12R2,0=102:'2eW<X:0o"). Qed.

Section Tr1.
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
Hypothesis MAL : malloc_contract RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Hypothesis H_LATCH : tr_latch_hyp XENV XENV_FP.
Hypothesis H_INCB : tr_incb_hyp XENV XENV_FP.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, CREDIT_DRV, g_read_stage in *; lia.

(* [comment removed for export] *)
Definition TPRE (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
    (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ CLX OUT_rep ERR_rep XENV LIB stdout_init m /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7
  /\ stk asegs m (rt_sp0 RT Σ - STACK_SPAN) (usp - 80)
  /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_SPAN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
  /\ rt_live RT Σ = [(buf, cap)] /\ rt_frames RT Σ = [] /\ CREDIT_DRV - 5 * cap <= rt_credit RT Σ /\ cap <= 67108864
  /\ buf <= cp /\ cp + 1 <= buf + cap /\ (0 < L -> bytes_at asegs m cp [c0b]) /\ 0 <= L < 32768
  /\ buf <= pp /\ pp + plen <= buf + cap /\ bytes_at asegs m pp payload /\ plen = Z.of_nat (length payload) /\ plen < 2^26
  /\ usp + 16 <= USTACK_TOP.

Theorem tr_start : forall (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
    (gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  TPRE Σ usp buf cap cp L pp plen c0b payload c0 c1 c2 c3 c4 c5 c6 c7 m ->
  cps asegs (ASTA RT Σ (PMfd fds0 fs)
               (eq (entry_st (Z_to_bv 64 0x96030) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1
                     (Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen) a4 a5 a6 a7 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11
                     t3 t4 t5 t6 F fc e_target_run m)))
    (TLOOP RT OUT_rep ERR_rep XENV LIB fs (tr_calls L c0b) stdout_init usp buf cap x0 x1 x2 x3 x4 x5 s6 s7).
Proof using AF AF_DRV MAL MCP OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img H_LATCH H_INCB.
  intros Σ usp buf cap cp L pp plen c0b payload gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    c0 c1 c2 c3 c4 c5 c6 c7 F fc m HP T c HA Hk.
  destruct HP as (ART0 & MI0 & CLX0 & FR0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & CR & CAPB & Hcp1 & Hcp2 & HC0 & HL
                  & Hpp1 & Hpp2 & BP & PL & PB & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  assert (INB : In (buf, cap) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m buf cap ART0 INB) as (PR1 & PR2 & PR3).
  pose proof (tr_calls_range L c0b) as TCR.
  set (lo := rt_sp0 RT Σ - STACK_SPAN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  assert (B16' : (usp - 80) mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 5); lia).
  assert (CSEG : SEGTOP_A <= cp \/ cp + 1 <= 0x10000) by (destruct PR3; [right| left]; lia).
  (* the target's prologue: the 80-byte frame below usp - 80 *)
  pose proof (tr_pro1 (usp - 80) cp L pp plen (Z_to_bv 64 0x96030) gp t0 t1 t2 x0 x1 a4 a5 a6 a7 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo ST0 ltac:(ul) ltac:(ul) B16' ltac:(ul) MI0) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ _ fs _ _ W1') HA).
  intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (a1j & m1 & -> & MU1 & WM1 & MI1 & TF1 & ST1) & Hc1').
  replace (usp - 80 - 80) with (usp - 160) in Hc1', ST1, MU1 by lia.
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 160) ART0); [ul| |exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB stdout_init m1).
  { apply (CLX_munch OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img _ m m1 _ CLX0 MU1 WM1).
    intros x Hx. cbn. split; [ul| exact I]. }
  assert (AGM1 : agree_on (fun x => usp - 80 <= x < USTACK_TOP) m m1)
    by (apply (agree_of_munch _ _ _ _ MU1); intros x Hx; cbn; split; [lia| exact I]).
  assert (BP1 : bytes_at asegs m1 pp payload).
  { apply (bytes_at_agree asegs m m1 _ _ BP). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. rewrite <- PL in Hx.
    cbn. split; [ul| exact I]. }
  assert (HC1 : 0 < L -> bytes_at asegs m1 cp [c0b]).
  { intros HLp. apply (bytes_at_agree asegs m m1 _ _ (HC0 HLp)). apply (agree_of_munch _ _ _ _ MU1). intros x Hx.
    cbn in Hx |- *. split; [ul| exact I]. }
  (* the guard latch on TR_INIT, inside XENV *)
  pose proof CLX1 as (_ & _ & XE1 & _).
  pose proof (AF_DRV Σ m1 ART1) as (_ & _ & GI1 & _).
  pose proof (H_LATCH (usp - 160) lo (Z_to_bv 64 0x96030) gp t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) (Z_to_bv 64 cp) a1j
                (Z_to_bv 64 pp) (Z_to_bv 64 plen) a4 a5 a6 a7 (Z_to_bv 64 L) x3 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
                XE1 GI1 ST1 ltac:(ul) ltac:(ul) ltac:(ul) MI1) as W2.
  lazymatch type of W2 with evt asegs _ ?X =>
    assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
  clear W2.
  apply (cps_realizes asegs _ _ _ cf1 (asta_evt RT AF Σ _ fs _ _ W2') Hc1').
  intros cf2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ cf2 Hc2)
    as (ms2 & (ra2 & b0 & b1 & b2 & b3 & m2 & Wx & -> & XE2 & HWx & MU2 & WM2 & MI2 & ST2) & Hc2').
  assert (WXS : forall x, in_ranges Wx x -> client_static x) by (intros x Hx; exact (proj1 (XENV_img x (HWx x Hx)))).
  assert (ART2 : ART RT Σ m2).
  { apply (af_frame RT AF Σ m1 m2 (usp - 160 - 48) ART1); [ul| |exact WM2].
    intros a Ha. apply MU2. cbn [outside]. split.
    - intros Hin. apply Ha. left. ul.
    - apply outside_of_not_in_ranges'. intros Hin. apply Ha. right; left. exact (WXS _ Hin). }
  assert (CLX2 : CLX OUT_rep ERR_rep XENV LIB stdout_init m2)
    by exact (CLX_xenv_update OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc LIB_loc IO_img XENV_img _ m1 m2
                (usp - 160 - 48) (usp - 160) Wx CLX1 MU2 WM2 ltac:(ul) HWx XE2).
  assert (OWX : forall x, SEGTOP_A <= x -> outside Wx x).
  { intros x Hx. apply outside_of_not_in_ranges'. intros Hin. pose proof (client_static_range _ (WXS _ Hin)). lia. }
  assert (AGM2 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m1 m2).
  { apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [outside]. split; [lia|]. apply OWX. ul. }
  assert (AGB : forall x, buf <= x < buf + cap -> outside ((usp - 160 - 48, usp - 160) :: Wx) x).
  { intros x Hx. cbn [outside]. split; [ul|]. apply outside_of_not_in_ranges'. intros Hin.
    pose proof (client_static_range _ (WXS _ Hin)). destruct PR3; ul. }
  assert (BP2 : bytes_at asegs m2 pp payload).
  { apply (bytes_at_agree asegs m1 m2 _ _ BP1). apply (agree_of_munch _ _ _ _ MU2). intros x Hx. apply AGB.
    rewrite <- PL in Hx. lia. }
  assert (HC2 : 0 < L -> bytes_at asegs m2 cp [c0b]).
  { intros HLp. apply (bytes_at_agree asegs m1 m2 _ _ (HC1 HLp)). apply (agree_of_munch _ _ _ _ MU2). intros x Hx. apply AGB.
    cbn in Hx. lia. }
  assert (FR2 : main_frame m2 usp c0 c1 c2 c3 c4 c5 c6 c7).
  { apply (main_frame_agree m m2 usp _ _ _ _ _ _ _ _ FR0); [| exact (wmono_trans asegs m m1 m2 WM1 WM2)].
    apply (agree_trans _ m m1 m2); [eapply agree_sub; [exact AGM1|]; intros x Hx; cbv beta in *; ul|].
    eapply agree_sub; [exact AGM2|]. intros x Hx; cbv beta in *; ul. }
  assert (TF2 : tr_frame m2 (usp - 80) (Z_to_bv 64 0x96030) x0 x1 x2 x3 x4 x5 s6 s7).
  { apply (tr_frame_agree m1 m2 _ _ _ _ _ _ _ _ _ _ TF1); [| exact WM2]. eapply agree_sub; [exact AGM2|].
    intros x Hx; cbv beta in *; ul. }
  destruct (Z.eq_dec plen 0) as [Z0|NZ].
  - (* empty payload: no allocation, d = TR_EMPTY *)
    destruct payload as [|b l]; [| cbn in PL; lia].
    clear PL BP BP1 BP2. subst plen.
    pose proof (tr_pro2_empty (usp - 160) cp L pp c0b ra2 gp t0 t1 t2 b0 b1 b2 b3 a4 a5 a6 a7 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  F fc m2 ltac:(ul) HL CSEG HC2 MI2) as W3.
    lazymatch type of W3 with evt asegs _ ?X =>
      assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
    clear W3.
    apply (cps_realizes asegs _ _ _ cf2 (asta_evt RT AF Σ _ fs _ _ W3') Hc2').
    intros cf3 Hc3. apply Hk.
    destruct (ASTA_unpack RT Σ _ _ cf3 Hc3) as (ms3 & (a0' & ->) & Hc3').
    exists Σ, 0, TR_EMPTY, 0, [], ra2, gp, t0, t1, t2, a0', b1, b2, b3, a4, a5, a6, a7, (Z_to_bv 64 cp), s8, s9, s10, s11.
    exists t3, t4, t5, t6, c0, c1, c2, c3, c4, c5, c6, c7, F, fc, m2.
    split; [exact Hc3'|].
    split; [| split; [exact TCR| unfold FUZZ_COST, CREDIT_DRV in *; nia]].
    split; [exact ART2|]. split; [exact MI2|]. split; [exact CLX2|]. split; [exact FR2|]. split; [exact TF2|].
    split; [exact ST2|].
    split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
    split; [rewrite LV; reflexivity|]. split; [exact FRS|]. split; [reflexivity|]. split; [lia|].
    split; [apply bytes_at_nil; unfold TR_EMPTY; lia|]. split; [intros _; split; reflexivity|]. split; [intros Hp; lia|].
    split; [lia| exact UT0].
  - (* copy the payload into a fresh allocation *)
    pose proof (tr_pro2_copy (usp - 160) cp L pp plen c0b ra2 gp t0 t1 t2 b0 b1 b2 b3 a4 a5 a6 a7 x5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6 F fc m2 ltac:(ul) HL ltac:(lia) CSEG HC2 MI2) as W3.
    lazymatch type of W3 with evt asegs _ ?X =>
      assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
    clear W3.
    apply (cps_realizes asegs _ _ _ cf2 (asta_evt RT AF Σ _ fs _ _ W3') Hc2').
    intros cf3 Hc3.
    destruct (ASTA_unpack RT Σ _ _ cf3 Hc3) as (ms3 & -> & Hc3').
    assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
    apply (MAL Σ (PMfd fds0 fs) (Z_to_bv 64 0x961f0) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
             (Z_to_bv 64 pp) (Z_to_bv 64 plen) b1 b2 b3 a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT)
             (Z_to_bv 64 (tr_calls L c0b)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 plen lo); try reflexivity; try assumption;
      try (match goal with |- _ - STACK_WIN <= lo => unfold lo, STACK_WIN; lia end).
    + apply PMfd_fdfs_only.
    + apply PMfd_mat_stable.
    + lia.
    + rewrite LV. reflexivity.
    + unfold mcost, CREDIT_DRV in *. destruct (Z.leb_spec plen 64512); lia.
    + intros _. rewrite LV. cbn [sec_bytes]. unfold SEC_BYTES.
      repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
    + unfold call_ok. rewrite EU2. split; [exact ST2|]. ul.
    + unfold unwind_ok. rewrite EU2, !unsigned_lit by ul. split; [cbn; tauto|]. left. ul.
    + intros cf4 (Σ1 & owned & Hc4 & LV1 & FRS1 & SP1 & CR1 & Pow & Pal & Ptop).
      destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & WR3 & ACC3) & Hc4').
      destruct RS3 as (u0 & u1 & u2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & u3 & u4 & u5 & u6 & F3 & fc3 & ->).
      rewrite EU2 in ST3, PRES3.
      rewrite (ret_pc_even 0x961f0) in Hc4' by lia.
      assert (INO : In (owned, plen) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
      assert (INB1 : In (buf, cap) (rt_live RT Σ1)) by (rewrite LV1, LV; right; left; reflexivity).
      assert (DISJ : owned + plen <= buf \/ buf + cap <= owned).
      { apply (af_live_disj RT AF Σ1 m3 owned plen buf cap [] [(buf, cap)] ART3); [rewrite LV1, LV; reflexivity| left; reflexivity]. }
      pose proof (af_live_range RT AF Σ1 m3 owned plen ART3 INO) as (OR1 & OR2 & OR3).
      assert (CLX3 : CLX OUT_rep ERR_rep XENV LIB stdout_init m3)
        by exact (CLX_pres OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                    _ m2 m3 _ _ _ CLX2 PRES3 WM3).
      pose proof (agree_stack_pres _ _ _ _ _ PRES3) as AG3.
      assert (BP3 : bytes_at asegs m3 pp payload).
      { apply (bytes_at_agree asegs m2 m3 _ _ BP2). apply (agree_of_pres _ _ _ _ _ _ PRES3). intros x Hx.
        rewrite <- PL in Hx. right; right; left. exists buf, cap. split; [exact INB| lia]. }
      pose proof (tr_copy_walk (usp - 160) owned gp u0 u1 u2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) d1 d2 d3 d4 d5 d6 d7
                    (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0b)) s6 s7 s8 s9 s10 s11
                    u3 u4 u5 u6 F3 fc3 m3 ltac:(ul) MI3) as W4.
      lazymatch type of W4 with evt asegs _ ?X =>
        assert (W4' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W4) end.
      clear W4.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W4') Hc4').
      intros cf5 Hc5.
      destruct (ASTA_unpack RT Σ1 _ _ cf5 Hc5) as (ms5 & <- & Hc5').
      apply (MCP Σ1 (PMfd fds0 fs) (Z_to_bv 64 0x96204) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 plen)
               (Z_to_bv 64 pp) (Z_to_bv 64 owned) (Z_to_bv 64 pp) (Z_to_bv 64 plen) d3 d4 d5 d6 d7 (Z_to_bv 64 owned) (Z_to_bv 64 cp)
               (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0b)) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F3 fc3 m3 owned pp payload lo);
        try reflexivity; try assumption; try (match goal with |- _ - STACK_WIN <= lo => unfold lo, STACK_WIN; lia end).
      * apply PMfd_fdfs_only.
      * apply PMfd_mat_stable.
      * rewrite <- PL. reflexivity.
      * ul.
      * ul.
      * lia.
      * rewrite <- PL. exact (checked_src_live RT AF Σ1 m3 _ lo buf cap pp plen ART3 INB1 ltac:(try unfold lo; unfold STACK_WIN in *; lia)
                                ltac:(try unfold lo; unfold STACK_WIN in *; lia) ltac:(rewrite SP1; try unfold lo; unfold STACK_WIN in *; lia)).
      * rewrite <- PL. exact (checked_dst_live RT AF Σ1 m3 _ owned plen owned plen ART3 INO ltac:(lia) ltac:(lia) ltac:(lia)).
      * rewrite <- PL. lia.
      * unfold call_ok. rewrite EU2, SP1. split; [exact ST3|]. ul.
      * intros cf6 Hc6.
        destruct (ASTA_unpack RT Σ1 _ _ cf6 Hc6) as (ms6 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BS4) & Hc6').
        destruct RS4 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
        rewrite EU2 in ST4, PRES4. rewrite <- PL in PRES4.
        rewrite (ret_pc_even 0x96204) in Hc6' by lia.
        assert (CLX4 : CLX OUT_rep ERR_rep XENV LIB stdout_init m4)
          by exact (CLX_pres_ex OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                      _ m3 m4 _ _ _ _ _ CLX3 PRES4 WM4 ltac:(intros x Hx; unfold SEGTOP_A in *; lia)).
        pose proof (agree_stack_pres_ex _ _ _ _ _ _ _ PRES4 ltac:(ul)) as AG4.
        pose proof (tr_copy_ret_walk (usp - 160) owned gp w0 w1 w2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) (Z_to_bv 64 owned) e1 e2 e3 e4 e5
                      e6 e7 (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0b)) s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m4
                      MI4) as W5.
        lazymatch type of W5 with evt asegs _ ?X =>
          assert (W5' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W5) end.
        clear W5.
        apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W5') Hc6').
        intros cf7 Hc7. apply Hk.
        destruct (ASTA_unpack RT Σ1 _ _ cf7 Hc7) as (ms7 & <- & Hc7').
        exists Σ1, plen, owned, owned, payload, (Z_to_bv 64 0x96204), gp, w0, w1, w2, (Z_to_bv 64 owned), e1, e2, e3, e4, e5, e6, e7.
        exists (Z_to_bv 64 cp), s8, s9, s10, s11, w3, w4, w5, w6, c0, c1, c2, c3, c4, c5, c6, c7, F4, fc4, m4.
        split; [exact Hc7'|].
        split; [| split; [exact TCR| rewrite CR1; unfold mcost, FUZZ_COST, CREDIT_DRV in *;
                                     destruct (Z.leb_spec plen 64512); nia]].
        assert (AG24 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m2 m4).
        { apply (agree_trans _ m2 m3 m4); [eapply agree_sub; [exact AG3|]; intros x Hx; cbv beta in *; lia|].
          eapply agree_sub; [exact AG4|]. intros x Hx; cbv beta in *; lia. }
        assert (AG14 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m1 m4) by (apply (agree_trans _ m1 m2 m4); [exact AGM2| exact AG24]).
        assert (WM24 : wmono asegs m2 m4) by exact (wmono_trans asegs m2 m3 m4 WM3 WM4).
        split; [exact ART4|]. split; [exact MI4|]. split; [exact CLX4|].
        split; [apply (main_frame_agree m2 m4 usp _ _ _ _ _ _ _ _ FR2); [eapply agree_sub; [exact AG24|]; intros x Hx; cbv beta in *; ul
                | exact WM24]|].
        split; [apply (tr_frame_agree m2 m4 _ _ _ _ _ _ _ _ _ _ TF2); [eapply agree_sub; [exact AG24|]; intros x Hx; cbv beta in *; lia
                | exact WM24]|].
        rewrite SP1. split; [exact ST4|].
        split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
        split; [rewrite LV1, LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); reflexivity|].
        split; [rewrite FRS1; exact FRS|]. split; [exact PL|]. split; [exact PB|].
        split; [exact BS4|].
        split; [intros Hp; lia|]. split; [intros _; reflexivity|]. split; [lia| exact UT0].
Qed.

End Tr1.
