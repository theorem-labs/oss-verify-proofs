(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (tr_iter's recorded proof replaced by a plain proof after leptonica/bilateral_fuzzer's text for the same driver, at this binary's addresses, over the stack floor lo := rt_sp0 - STACK_SPAN, the span the start state guarantees writable, with the callee's floor rt_sp0 - STACK_WIN below it). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_frmkit D_iface D_defs D_kit D_libiface D_clx D_rlkit D_trdefs D_trpro D_trwalk.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_D_tr2 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53B238RT_iface9in_rangesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface=client_staticC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K53B235D_clxCclient_static_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3notC69OSSVerify5KrLib2K53B235D_clxIoutside_of_not_in_ranges'C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53B238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53B236D_defs8drv_cellC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_clx7LIB_imgC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c69OSSVerify5KrLib2K53B235D_tr2Doutside_image_rangesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:D_libiface6LIB_FPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify5KrLib2K53B236D_defs7TR_INCBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs3CLXC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53B235D_kit>agree_of_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53B235D_clx?drv_cell_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_clx@drv_cell_not_libC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit@agree_of_pres_fpC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C69OSSVerify5KrLib2K53B235D_kit;agree_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_clxHnot_in_ranges_of_outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_clx@agree_ranges_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit9agree_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib2K53B235D_kit>ro_cells_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53B235D_kitArw_cells_agree_nwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit<stk_agree_nwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface:rt_pres_fpC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53B237D_iface9SSP_GUARDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs7ERRNO_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236Layout<g_read_stageC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I69OSSVerify5KrLib2K54Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B235D_tr2;incb_staticC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C69OSSVerify5KrLib2K53B238RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib4Init5Peano2ltC69OSSVerify5KrLib2K53B238RT_iface8so_linesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238D_trdefs5TLOOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53B238RT_iface:emit0_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238D_trdefs5TFREEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface3rtsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface4PMfdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238D_trdefs4TCTXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9rt_creditC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs:main_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238D_trdefs8tr_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K53B238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238D_trdefs7tr_liveC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53B238RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib2K53B238RT_iface=af_live_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface=af_live_alignC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib6ZArith6BinInt1Z3divC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238D_trwalk?tr_loop_in_walkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9emit0_outC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs8asta_evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs;ASTA_unpackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8af_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit9stk_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit>bytes_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface>PMfd_fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs?PMfd_mat_stableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init9Datatypes3appC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib2K53B238RT_iface9sec_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00C69OSSVerify5KrLib2K53B236D_defs7drv_sspC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC69OSSVerify5KrLib2K53B238RT_iface6ret_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface:rt_after_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B235D_tr2>LIB_outside_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237D_rlkitCagree_stack_pres_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238D_trwalk@tr_fuzz_ret_walkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B235D_tr2>CLX_around_libC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53B235D_clx:CLX_io_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface7call_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8rt_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_clx6CLX_ioC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B235D_tr2=IO_outside_hiC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit>rw_cells_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238D_trwalk@tr_emit_ret_walkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238D_trdefs=TCTX_agree_nwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS<cps_realizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS4cpsEC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Canon3evwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3eqbK46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib2K54Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:D_libiface9FUZZ_COSTC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib2K53B238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs8TR_EMPTYC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib2K53B23:D_libiface6e_fuzzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9e_vprintfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify5KrLib2K53B238RT_iface6e_freeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53B236D_defs4fds0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs4TP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs7TR_INITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238D_trdefs5TR_M2C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02C69OSSVerify5KrLib2K53B23:D_libiface6RA_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:D_libiface9FUZZ_LIVEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8LIVE_MAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:D_libiface9FUZZ_SECBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9SEC_BYTESC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_preorderC69OSSVerify5KrLib2K53B23:D_libiface:FUZZ_STACKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8FMT_emitC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C69OSSVerify5KrLib2K53B238RT_iface8RT_STACKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238D_trdefs5TR_M1C1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section Tr2.
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
Hypothesis FUZZ : fuzz_one_cps RT LIB.
Hypothesis VPR : vprintf_emit0_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Hypothesis H_LATCH : tr_latch_hyp XENV XENV_FP.
Hypothesis H_INCB : tr_incb_hyp XENV XENV_FP.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, g_read_stage in *; lia.

Lemma outside_image_ranges : forall (W : list (Z * Z)), (forall x, in_ranges W x -> client_static x) ->
  forall x, SEGTOP_A <= x -> outside W x.
Proof.
ltac2:(KReplay.run1 (kr_t_D_tr2 ()) ["Tr2"] "h04__p1h14__p2h24__x1h34__x2h41xh51Hh62HWh73Hinh82Hxh91Wh:7__arithh;4__ffh<8__varmaph=5__witp;2p;1p;4p;7p;3p;6p;8p10000p4p7210R0p1000\p4p710p8P0p10018p4p710p8g001Vj2RTg0026j1;Tg002Vj29Tg003Tj1?Tg004Vj21Tg0052j2ITg0067j12Tg006\j1ATg007:j2:Tg007Vj28Tg0081j1=Tg008Qj2<Tg008oj1QTg009Mj4PTg009kj1OTg00:Ij1HTg00;4j26Tg00;Wj47Tg00<Bj7DTg00<fj1CTg00=Hj2BTg00=jj2ETg00>Dj2FTg00?0j3GTg00?Jj3@Tg00?ij4JTg00@[j1KTg00A4j3>Tg00B?j6LTg00Bcj7MTg00CGj8NTf0R0#2#2p=0f1R1g00CkR2g00DJR3P3g00DjR4P0ELp=5P1P2P3P3P4P0g00EJFMp=4f3R5P2P3P3P4f2R6P1P0GNp=3g00EjR7/R7#;1910%?1[^47g00FHR8/101951R9P5P6P0O2,I6g00GER:#2R;#2#0#0#0#0#0#0#0#AR</161:68'8p-0R=g00GjR>#=%;>P71<76P1%Q7CP%O7%H7R>P>P2P3P3P4f4R2,5>P7167;R;g00HV167:R:C7,4>FD%C3R3P>P7P:g00I=P;C7,4>P3f5R3,5>C3C31B>4P0P6g00IdR>g00JDR4'E1F06=G>4dg00Jd=@71CJb;b<b=X27X37X0=W11:10,861116P3[[^27^37^0=^1=P0g00KB11<2P2P8P1P5O6b:b5W7%K9e9>51W8X47W6W9o"). Qed.

Lemma LIB_outside_hi : forall x, SEGTOP_A <= x -> outside LIB_FP x.
Proof.
ltac2:(KReplay.run1 (kr_t_D_tr2 ()) ["Tr2"] "h02Hxh11xp;2p;1p;3g002Vj26Tg003Tj15Tg00K_j10Tg00@[j11Tg00LZj24Tg00MSj32Tg00Mnj23Tg00O4R0g00Ejf0R1,60f1R0#5%00#1140132W0W1'3o"). Qed.

Lemma IO_outside_hi : forall x, SEGTOP_A <= x -> outside IO_FP x.
Proof using IO_img.
ltac2:(KReplay.run1 (kr_t_D_tr2 ()) ["Tr2"] "h02Hxh11xp;2p;1p;3g002Vj27Tg003Tj16Tg00K_j10Tg00@[j11Tg00P1j25Tg007Vj22Tg00MSj33Tg00Mnj24Tp,5IO_FPR0g00Ejf0R1,70f1R0#6%00#1g00O4/50'2p,6IO_imgP0P1O233W0W1'4o"). Qed.

(* [comment removed for export] *)
Lemma incb_static : client_static TR_INCB /\ ~ drv_cell TR_INCB /\ outside IO_FP TR_INCB /\ outside LIB_FP TR_INCB.
Proof using XENV_img H_INCB.
ltac2:(KReplay.run1 (kr_t_D_tr2 ()) ["Tr2"] "h04__x1h11mh21xh37__arithh44__ffh58__varmaph65__with71ah82m'p;1p;2p;3p;4p;7p;5g0067j10Tg00Pjj1<Tg00QHj1;Tg00Qkj1@Tg00RMj2=Tg002Vj2:Tg004Vj22Tg006\j1DTg00S7j28Tg007:j23Tg007Vj21Tg00@[j1>Tg00?0j39Tg00STj2STg00T:j1RTg0081j17Tg00U2j3QTg00URj44Tg00VKj3Pj5NTg0026j1ITg008Qj2HTg009kj1FTg00:Ij1CTg00;4j2ETg00;Wj46Tg00Vfj2BTg00WIj3GTg00<Bj7ATg00=Hj2JTg00=jj2KTg00>Dj2?Tg00?Jj3LTg00?ij4MTg00Bcj7OTf1R0g00CkR1g00DJR2P2g00DjR3f0R4g00EJFOp=5p,8XENV_imgg00WlR5g00GER6#0#0#0R7#0#0#0#<R8#;R9%<7R7#;#@R:[R;P:^29p,4XENVR<P0O1p,7XENV_FPR=1=84':1=80R8,25%D6R>,85R?,38'1#>f4f2R8O1f5P8O159:[[^79g00XfR9P8P5g00Y^R:g00JdR@,S7#R%7:3QR:C4P<f3O1[[[]8]1R7g00EjRA1254134?'11:=0[]2R=P<P4O1P9P0P5P:C4[^1;117=p,6H_INCB3PP5g00GjR=#7%I=1HA0%FA%CAR=P1P2P2P3PA1EA6R6g00I=P6C6,5=PAP6g00HV1BA>9GA6C6,5=FA1J=3P4P8g00IdR=g00JDR3'K1?48=9=3dALA@0CMb4b5b6X0A1244184>,34'1^0AP4P5O1b3DNO2o"). Qed.

(* [comment removed for export] *)
Lemma CLX_around_lib : forall so m m1 m2 m3 live frames sp flo fhi,
  CLX OUT_rep ERR_rep XENV LIB so m ->
  munch [(TR_INCB, TR_INCB + 1)] m m1 ->
  rt_pres_fp live frames sp LIB_FP m1 m2 -> LIB m2 ->
  munch [(flo, fhi); (TR_INCB, TR_INCB + 1)] m2 m3 -> SEGTOP_A <= flo ->
  rw_cells asegs m3 TR_INCB [C1 (Z_to_bv 8 0)] ->
  CLX OUT_rep ERR_rep XENV LIB so m3.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img H_INCB.
ltac2:(KReplay.run1 (kr_t_D_tr2 ()) ["Tr2"] "p'0h01xi001xh11Hh21vh34__x1h44__x2h51gh62Hxh77__arithh84__p1h94__ffh:8__varmaph;5__with<4__p2h=2_Hh>1mh?2H0h@2HrhA1ahB1nhC1zhD2HahE2HnhF4__x3hG2lohH2AGhI4AG01hJ4AG12hK4AG23hL3AGDhM2CShN2ERhO3FLOhP2H1hQ2H2hR2H3hS2H4hT2HdhU5INCB3hV3IS1hW3IS2hX3IS3hY3IS4hZ3ISRh[2L2h\3MU1h]3MU3h^4NDRVh_3NIOh`1Pha2PRhb2RShc2SGhd3fhihe3flohf6frameshg4livehh2m'hi2m1hj2m2hk2m3hl2sohm2sphn1yp%0p&0p;1p;2p;6p;4p;3p;9p;8p;7p;<p;Bg0067j1UTg00Pjk100Tg00QHj1zTg00Qkk10bTg001Vk20;Tg0026j1nTg00ZVj6>Tg00[Lj1kTg0081j1iTg00\DR0j2;Tg00\^j1rTg006\j1gTg00S7R1j28Tg00]Vj4oTg00U2j3]Tg00^6j3ATg00STk20NTg00T:k10MTg003Tj1PTg00K_j1?Tg00@[j1HTg00P1j2:Tg007VR2j20Tg0052j2jTg002Vj22Tg00^mS00j21Tg007:R3j26Tg008Qj2sTg008ok10YTg009Mj4aTg009kk10XTg00:Ik10WTg00;4j2fTg00Vfj2eTg00<fk10TTg00=Hk20STg00=jj2MTg00>Dk20RTg00?0j3_Tg00?Jk30QTg00?ik40PTg004Vj23Tg00_Gj45Tg00_bk606k80FTg00`bj3^Tg00a\j4\Tg00bXk205Tg00cTk204Tg00dRk202Tg00MSj3[k80HTg00eWj3YTg00f1j3VTg00VKj3STg00fKk201Tg00gLk20LTg00hNm90KTg00iPj1KTg00ioj2lTg00jXj3~Tg00kAk20JTg00kmj6}Tg00;Wj4pTg00ljj4{Tg00n4k60ITg00RMj2uTg00LZk20GTg00o6j6wTg0101j1bTg010mR4j1NTg011Mj1hTg011kk40ETg012Nj6|Tg0137k408Tg013^k10CTg014Ck70BTg015Ck40<Tg015]k70@Tg016`k70OTg017^k40?Tg00URk407Tg018Wk409Tg019Lk60>Tg00Bck70UTg00WIk30VTg00<Bk70aTg01:Kk60`Tg00CGk80_Tg00B?k60^Tg000\k60]Tg01:om<0[Tg01;TmB0=Tg01<:m<0ZTg01<_k70\Tf0R5#U#Up=Wg00Y^R6f1R7;]5p=Og00XfR8P7g01=CR9P5H0?p=7P8P7g01>@R:P5H07p=4f3R;f2R<';P8P7g01?:R=P5H09'0p=<1075,0<p=If4R>P;P<g00O4R?P7P5J0>p=Df5R@g00EjRAPAP>P;Co;]<?A75p=Bg00FHRB/35p=FP8P7g00WlRCP5H07p=@1;<7/05p=XP8P7P=P5H09p=d13;<1675'0p==13C7/05p=v13C5p=R1675,0<#Hp=CPAP7g00I=P5Cpp=`P7g00CkRDg00DJREPEg00DjRFP5g00EJK0Up=9B0VA75p=TPAP7g00HVP5Cpp=QP<PDPEPEPFP7P5K0ap=LP7PDPEPEPFP5J0`p>0:P;PDPEPEPFP<P7P5L0_p=J1875,6<,0;p=E1675,0<p=GPAPAP<P7Co=];5p=cP7PDPEPEPFP5J0^p=m13<7/05p=tPAP;P<P7PCP5J0]p=q1875,6<p=yg01@9S01PAPAPAP4P4P@P>P;P<P7P5N<0[p=xPAPAPAPAPAPAP1f7R4f6RGP@P1P>P9P9P;P<P7P5NB0=p>0DPAPAP3P4P3PGP@P>P;P<P7P5N<0Zp>03P<PDPEPEPFP7P5K0\p=ZPAPAPAPAPAPAP1P4PGP@P1P>P:P:P;P<P7P5NB0=p>0Ag01@Xg00GER1#URD#US02#US03#U#WR3$00RH#zRIQ03$00RJ#z$0bS04[RK20;AARL#nQ01-0;A#np,7OUT_repRMp,7ERR_repRNp,4XENVROp,3LIBRPf9RQf8RRE>P2PMf:RSPQO2PNPQO1POPQO1PPPQO1%k5%i6R6'ORT,7SX5I,;IPI%r5/O6RU,4SX2IPQ%W3#W#W#W#W#gR3,8=RVC<3I3IPAPAPC%g1RW,8CRXCo%iL5]LRY?ASQP4PGP@PSPQDDPPPSO1PLPGP@PYf;RZPSEB%F4f<R[g00JdR\-0NJ$0M/O6RJ'@PMPNPOPPfAR]f=R^E>[[[[[[P5PMP[PZO2PNP[O1POP[O1PPP[O117^TX5I,;IPI14^UX2IP[PVC<3I3IP2PNP^O1POP^O1PPP^O1f>R[/7TX5IPI14[UX2IP^PVC<5XI3IAAY[^PZPSPQP[P^DDPPP[O1PLPSPQPYf?R_P[EB%FZf@RZ/@JPMPNPOPPfER`P]E>[[[[[[P5PNP_O1POPZO1PPPZO117]TX5IPI14]UX2IPZPVC<5XI3IP2POP]O1PPP]O1fBRZ/7TX5I,;IPI14ZUX2IP]PVC<3IAAYZ]P_P[P^PZP]DDPPPZO1PLP[P^PYfCR^PZEB%F_fDRa/@JPMPNPOPPfIRbP`E>[[[[[[P5POP^O1PPPaO117`TX5I,;IPI14`UX2IPaPVC<3IP2PPP`O1fFRc/7TX5IPI14cUX2IP`PVC<5XIAAYc`P^PZP]PcP`DDPPPcO1PLPZP]PYfGR]PcEB%F^fHS05/@JPMPNPOPPfMRZPbE>[[[[[[P5PPP]O117bTX5IPI14bUX2IQ05PVC<5XIP2fJRd/7TX5I,;IPI14dUX2IPbPVC<AAYdbP]PcP`PdPbDDPPPdO1PLPcP`PYfKS06PdEB%F]fLS07/@JPMPNPOPPfQR]PZE>[[[[[[P5Q07/7TX5I,;IP0PI17ZTX5IPIfNRc/4UX2IPZPVC<AAYcZQ06PdPbPcPZDDPPPcO1PLPdPbPYfORdPcEBQ06#FfPRe/@JPMPNPOPPfURfP]E>[[[[[[[P517dTPI14]UX2IPePVC<P2fRRe/4UX2I,;I1d]VAAYe]PdPcPZPeP]DDPPPeO1PLPcPZPYfSRgPeEB%FdfTRh/@JPMPNPOPPfYRiPfE>[[[[[[P514hUX2I,;IP0PI14fUX2I1dfVfVR0=AYfPgPeP]P0PfDDPPP0O1PLPeP]PYfWS08P0EB%FgfXRg/@JPMPNPOPPf]PiE>[[[[[[[P5Q08/4U1dgVAAYigP0PfPhPiPgDDPPPiO1PLPfPhPYfZPiEB%F0f[/@Jg01AV%PCS09%?C#HS0:p,5IO_FPRi/:CS0;1:?CS0<'0S0='0S0>'0P2Q09Q0>PMPNPOPPfbRhf^E>P5Q09Q0>P2Q0:Q0=PMPNPOPPffRgPhE>P5Q0:Q0=P2Q0;Q0<PMPNPOPPfjRhPgE>P5Q0;Q0<1jCQP3PCPCPBC=12i5Rgp,7XENV_FPR]/25%?5Re'1'1165X,v5S0?#H'0X0Ap-0Rj^0APYfnRkfmRlP5PaP7P5O1P212i7S0@12]7S0A%?7Rm'1S0B'1S0C167X,v7S0D#HRn1:Y<P512i;12];%?;'1'1S0E%R>?C>XS0F%R@?C@XRog01BSRpg00GjS0G#iRqQ0G#nRrPA1sA<S0HP7&0YAS0ICaS0J&0XARs&0WARt1fA1Ru1fADRD'`,9tRv1eAWS0K,Tu,QD,9t5Lt-0:tRw&0TEREPwCJ20StFRFP5P<g00IdRwg00JDRx'M20R5<=_wxdB0QA\7H0PR\b9b:b;X3AX4A1357S0LP7P5PWCEg00KBS0M[137<S0N187WS0O7G<Q0M[[^3A^4AP5PGPCP7O3b7g01BoS0PC5S0Q1:Y@eW6W=P7P5O2n2001000000121000000W1X0AJ06A^5klfkS0RPhfiS0SP?PkPlP7PaP<P5O1P2Q0CPnPkPlflS0TP<C\1:?<'0P5Q0EQ0012i>12]>%?>'1frRafqRhfpS0UPGC\1:?G'0\oP512i@S0V%RG?CGXfsRWPaPhP4C\1:?4RxPhP4P4g01CKRwC=%P4Ry205W4204a4202a4'1'1Rz'1%?4S0W#HR{/0xR|p,6IO_imgS0XP4P7O2R}5[y9Yyz3VASy|}9S{xC5W=W6P5O112]@%?@'1S0YQ0012]GS0Z%?GS0[%R4?C4XftR{PWPaPRC\1:?R'0[P512]4S0\%RR?CRXS0]fuRxP{PWPQC\S0^1:?QR}PWPQPQPwC=S0_%PQRw205xQ204{Q202{Q'1'1Rz'1S0`%?Q#HS0a1:iQS0b/0}S0c'0R~p,8XENV_imgS0dPQP7O2S0e5[w9Ywz3VQ0bQ0aQ0cQ0e9Sw~3S7S}C5W=W6P5O1Q0WQ0]Q0^P}Q0_Q0`201Q79Ywz3V20LQ7C5W=W6P5O1n200100000021000010000W1P5O1n200100000021000011000W1P7P5O2n2001000000121000000W1X0AN90KA^7klPLQ0SfhRzPYCcPkPlP<P^P;P5O1P2Q0CPnPLQ0TQ0RPYCc/:<P5Q0EQ0FfoR2/3@?C@k10opQ00Q0VQ0Y%PGP712iGQ0XP4P5O29[y|W6P5O1Q0ZQ0['1Q00Q0\Q0W%PRP512]RQ0dPQP5O29[w~W6P5O1%?R201Q5W6P5O1n200100000021000010000W1P5O1n200100000021000010000%P@1jG5P3PGPGPBC=Q0Gg01DJR~#KRw#KR|,lA1lAw1lA~5~A5~Ag01Di+0J;]qPrPAPA1sA;P<Q0ICaP7Q0ICaPsPt1mt@R~Q02,fARw,QD,9t5LtPEPt1`wu,9tPE1mtG9Ltv-0:tCJCJPFP\b9b:b;X3AX4AXFAX8jX<jRyAG;7<13;7At<;GQ0M[[[^3A^4A^FA^8j^<jR4P516Rh133RPBPRPaP7Q06O7b7b1bMQ0QC5PLP2PkPYCcRR/:@eWEW6P7P5O2n2001000000121000000W1X0AJ06A^<klP;PhQ0UPkP<P;Q0UP2PkP7P5E}E}A^;hkQ0DPiPCPSPqPrQ0JPsPt1`Du,9tQ0K,TD,Qu,9t5LtPEPAPug01EUPDCp,9tCJPFP\b9b:b;X3AX4ARS1375RkQ0O7G5A_A7<[^3A^4AR2P5PCP;P7O3b7RlA_A<CRoP;PgXCAP<P5Cqb1C{W@PneX6gX0APn\g^0AQ0DP_PlPoP;PeXCAP<P5Cqb1O1W@PneX6eX0APn\e^0APMPxPhO2PNPhO1RNPOPhO1RMPPPhO1RP17aTX5IPI14aUX2IPhPVC<5XIRe'0Ro'0Rl'0p,7OUT_locPxP{PhPzPGPiP{PhP<Q0CPnQ0@Q0B;Y5P;P7P5O2C5X6gX0AJ0IRgO5PNPlp,7ERR_locP{PhfdPgO4PMPoQ04^0IPOP7O11uH5Ro,2]RM1uH7Rg#R?CgXRgQ04P>P<O1P@P<O13_[[^AI1@<JPOP;O1[[[]h^>KRlQ0?Q0A[^0ARNPOP5O11@7J[^>K10lNp,6H_INCB3SP{Phf`P@P<1uH<RH,2iRi12]HR]%?HRN'1Rl'1%RH?CHXAY]N79VilP5C5O2XEgXDMXAIP`L0HPPPep,7LIB_locPaPhQ0512?oPRP{PW12?5RRX0APb%P7%Hm20G753[,j7P3P7P7PBC=13a<?C<h16<X,v<RX#HRb/0pPyP4P516;a133;PBP;PWP7Q07O7b7PbPpP?PCP[PSP2P5PCP>P7O3b7A_A;CP>PRXCAP;P5Cqb?C{X@XPbeQ0PC5C5b1PLPhQ0UPYCc/:7eX6RX0AP7P5L0FWDXAIO4Ay5<79t<5Pm[^0ARRPQAy5;<9t;5RQX0ARYfwRhP{P@Q0CPnQ0@Q0BQ0AP<P7P5O2Rn7Vm3VP@P7PnO2C5X6QX0AEwWTXBAXGAA^Yh{\R^BA^GA17WTX5IRT,;I14WUX2IRW,;IRU1daVRR'0PIPTP0P8PxPaP9%k0/O6R0PfP5P9%b0#N1395R0%K|#KR|#K#K#K#KRf#NRT,89Rh7G51397RY167hR{'0Q03#gRQ,89Rn9GY7R@PYP{PYP5X0AR{PQO1Rm,89RL,67%hYP{1675#hXnAX0ARYP7P71MA7RbPhPLP{P{P{PAPAg01F<1875H0E,MAX>AXBARL1MA9PTPmP{P{Q01%N5,MAW0RmPfPQ1MAQExL0DL03E|P5H08P@PqPrPA1sA7P<Q0HCaPsPt&0C1,fAR1/`D,9t1eAQ,T1,QD,9t5LtR1PE1mt>RfAZt1~5ZtCJPFP\b9b:b;X3AX4AX8jX<jPkP5P7PQCE13<7R1P7P<PQCE/1>,1;[^3A^4A^8j^<jP5P=P;P;PVC=RQP:P;P;Q02#gRT,8:RhC=P9P;P7O5b7b?UX0AP0P5P9Q08#k/O6#b#NCE13:7R0?G7hRXP=P7P7PVC=,1@'1R@[^0AeO3K0BH0<PUPRPIPWPcP8PxPaP:%rc/O6RcPZP5P:%bc#N13:5Rc%N|RZ,8:RW7G5167WRR,00PXP0PRP0P{PTO1RR,8:RU,67%h0P{PYP7P7PbPWPUP{P{P{PL1MA:PZPRP{P{PmP|PT1MATExL0AL03E|P5H08PXPqPrQ0JPsPt1eAT,Tu,QD,9t9LtvRXPEAZtXfCJPFP\b9b:b;X3AX4AX8jQ0LP7P5PTCEQ0NP<P7PTCE/1;[^3A^4A^8jP5P9P;P;PnC=/1QP;P:P7O4b7b?UX0APcP5P:%rd/O6#b#NCEP@[^0AeO3K0@H0<P8PxPaP=PVQ07P=P5P5PVC=RVX0AR8P8PxPaP5P=P3PqPrPAQ0JP<Q0ICaPsPt1`wD,9t1eA3Ra,Tw,QD,9t5LtRwPEAZt~w9ZtfCJPFP\b9b:b;X3AX4AX8jX<j1873Rf9Gk5P1P7P<P3CE,1>,1;[^3A^4A^8j^<jP5P9P<P<PnC=P:P<P<PhC=P=P<P7O5b7VVX0AO3PqPrQ0JPsPt1Tua,QD,9t9LtvRvPEPvCJPFP\b9b:b;X3AX4AQ0LP7P5P3CEQ0N?G<f[^3A^4AP5P<P=P7O3b7VVX0AP8P7O1\V^0AeEwK0OC5C5bLC5C5C5C5b^b_bHbKbJbIb`bZWYWXP7P5O2n2001000000121000000W1WWP7P5O2n2001000000121000000W1WVP7P5O2n2001000000121000000b1WUWOW]W[WaW\WbWNX2IP7P5O2n2001000000121100000W1P7P5O2n2001000000121000000W1WcX5IP7P5O2n2001000000121100000W1P7P5O2n2001000000121000000W1WSP7P5O2n2001000000121000000W1WRP7P5O2n2001000000121000000W1WQP7P5O2n2001000000121000000W1WPP7P5O2n2001000000121000000W1XdAXeAXmAWfWgXkKXjKXiKW>Wlo"). Qed.

Theorem tr_iter : forall k so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7, (so = stdout_init \/ exists j, (j < 499)%nat /\ so = so_lines j) ->
  cpsE asegs (TLOOP RT OUT_rep ERR_rep XENV LIB fs k so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7) (evw 1 (emit0_out so))
    (fun c => (1 < k /\ TLOOP RT OUT_rep ERR_rep XENV LIB fs (k - 1) (emit0_next so) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 c)
              \/ (k = 1 /\ TFREE RT OUT_rep ERR_rep XENV LIB fs (emit0_next so) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 c)).
Proof using AF AF_DRV FUZZ VPR OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img H_LATCH H_INCB.
  intros k so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 Hso T c HL Hk.
  destruct HL as (Σ & plen & d & owned & payload & ra & gp & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3
                  & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7
                  & F & fc & m & HA & HT & Hk14 & HCR).
  pose proof HT as (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof incb_static as (IS1 & IS2 & IS3 & IS4).
  pose proof (client_static_range TR_INCB IS1) as ISR.
  set (lo := rt_sp0 RT Σ - STACK_SPAN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
  assert (DPOS : 0 < d /\ ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length payload) <= p + n /\ d mod 8 = 0)
                           \/ payload = [])).
  { destruct (Z.eq_dec plen 0) as [Z0|NZ].
    - destruct (P0 Z0) as [-> _]. split; [unfold TR_EMPTY; lia|]. right. destruct payload; [reflexivity| cbn in PL; lia].
    - rewrite (P1 ltac:(lia)).
      assert (IN : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
      pose proof (af_live_range RT AF Σ m owned plen ART0 IN) as (R1 & _).
      pose proof (af_live_align RT AF Σ m owned plen ART0 IN) as AL16.
      split; [lia|]. left. exists owned, plen. split; [exact IN|]. split; [lia|]. split; [lia|].
      apply Z.mod_divide in AL16; [| lia]. destruct AL16 as (q & ->). replace (q * 16) with ((q * 2) * 8) by ring.
      apply Z.mod_mul. lia. }
  assert (DOUT : forall x, d <= x < d + plen -> (x < 0x10000 \/ SEGTOP_A <= x) /\ x < rt_sp0 RT Σ - STACK_WIN).
  { intros x Hx. destruct (Z.eq_dec plen 0) as [Z0|NZ]; [lia|]. rewrite (P1 ltac:(lia)) in Hx.
    assert (IN : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
    pose proof (af_live_range RT AF Σ m owned plen ART0 IN) as (R1 & R2 & R3).
    split; [destruct R3; [left| right]; lia| lia]. }
  pose proof CLX0 as (O0 & ERR0 & XE0 & L0 & (g & SG0) & _).
  pose proof (proj1 H_INCB m XE0) as INCB0.
  (* the loop head sets TR_INCB to 1 *)
  pose proof (tr_loop_in_walk (usp - 160) ra gp t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 d) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3
                (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 TR_M2) s8 s9 s10 s11 t3 t4 t5 t6 F fc m INCB0 MI0) as W0.
  lazymatch type of W0 with evt asegs _ ?X =>
    assert (W0' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W0) end.
  clear W0.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ _ fs _ _ W0') HA).
  intros cf0 Hc0.
  destruct (ASTA_unpack RT Σ _ _ cf0 Hc0) as (ms0 & (m1 & -> & MU1 & WM1 & MI1 & INCB1) & Hc0').
  assert (AG1 : agree_on (fun x => ~ (TR_INCB <= x < TR_INCB + 1)) m m1)
    by (apply (agree_of_munch _ _ _ _ MU1); intros x Hx; cbn; split; [exact Hx| exact I]).
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 160) ART0); [ul| |exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. right; left.
    replace (bv_unsigned a) with TR_INCB by lia. exact IS1. }
  assert (L1 : LIB m1).
  { apply (LIB_loc m m1 L0). intros a Ha. apply AG1. intros Hin. apply (not_in_ranges_of_outside _ _ IS4).
    replace TR_INCB with (bv_unsigned a) by lia. exact Ha. }
  assert (SG1 : ro_cells asegs m1 SSP_GUARD [C8 g]).
  { apply (ro_cells_agree asegs m m1 _ _ SG0). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [| exact I].
    intros Hin. apply IS2. unfold drv_cell. replace TR_INCB with x by lia. right; left. exact Hx. }
  assert (ST1 : stk asegs m1 lo (usp - 160)).
  { apply (stk_agree asegs m m1 _ _ ST0); [| exact WM1]. eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. ul. }
  assert (BD1 : bytes_at asegs m1 d payload).
  { apply (bytes_at_agree asegs m m1 _ _ BD). eapply agree_sub; [exact AG1|]. intros x Hx. rewrite <- PL in Hx.
    pose proof (DOUT x Hx). cbv beta. lia. }
  apply (FUZZ Σ (PMfd fds0 fs) (Z_to_bv 64 RA_TOP) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
           (Z_to_bv 64 d) (Z_to_bv 64 d) (Z_to_bv 64 plen) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_INIT)
           (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 TR_M2) s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 d payload lo);
    try reflexivity; try assumption; try (match goal with |- _ - STACK_WIN <= lo => unfold lo, STACK_WIN; lia end).
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - rewrite <- PL. reflexivity.
  - exact (proj1 DPOS).
  - lia.
  - exact (proj2 DPOS).
  - intros p n Hin. rewrite LV in Hin. unfold tr_live in Hin. destruct (Z.eqb_spec plen 0) as [E|E]; cbn [app In] in Hin.
    + destruct Hin as [Hin|[]]. injection Hin as <- <-. exact (proj1 CAP0).
    + destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-; [lia| exact (proj1 CAP0)].
  - rewrite LV. unfold tr_live, LIVE_MAX, FUZZ_LIVE. destruct (plen =? 0); cbn; lia.
  - unfold FUZZ_COST in *. nia.
  - rewrite LV. unfold tr_live, FUZZ_SECB, SEC_BYTES. destruct (plen =? 0); cbn [app sec_bytes];
      destruct (64512 <? cap); try destruct (64512 <? plen); lia.
  - left. rewrite EU, unsigned_lit by lia. ul.
  - exact (drv_ssp m1 g (AF_DRV Σ m1 ART1) SG1).
  - rewrite EU. exact ST1.
  - rewrite EU. ul.
  - rewrite EU. ul.
  - rewrite EU. apply Z.mod_divide; [lia|]. apply Z.mod_divide in B16; [| lia]. destruct B16 as (q & ->). exists (q - 10). lia.
  - rewrite EU. lia.
  - intros cf1 (Σ1 & Hc1 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m2 & RS1 & (ART2 & MI2 & ST2) & PRES2 & LIB2) & Hc1').
    destruct RS1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    rewrite EU in ST2, PRES2.
    rewrite (ret_pc_even RA_TOP) in Hc1' by (unfold RA_TOP; lia).
    pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES2 ltac:(intros x Hx; apply LIB_outside_hi; ul)) as AGS2.
    assert (INCB2 : rw_cells asegs m2 TR_INCB [C1 (Z_to_bv 8 1)]).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ INCB1). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2). intros x Hx.
      cbn [cells_size csize Nat.add] in Hx. replace x with TR_INCB by lia. split; [right; left; exact IS1| exact IS4]. }
    pose proof (tr_fuzz_ret_walk (usp - 160) gp t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 owned) s3 (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 TR_M2) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m2 lo
                  (Z_to_bv 8 1) ST2 ltac:(ul) ltac:(ul)
                  ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia)
                  ltac:(ul) INCB2 MI2) as W1.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m3 & junk & -> & MU3 & WM3 & MI3 & EF1 & EF2 & EF3 & ST3 & INCB3) & Hc2').
    assert (CLX3 : CLX OUT_rep ERR_rep XENV LIB so m3)
      by exact (CLX_around_lib so m m1 m2 m3 _ _ _ (usp - 160 - 80) (usp - 160) CLX0 MU1 PRES2 LIB2 MU3 ltac:(ul) INCB3).
    pose proof CLX3 as (OUT3 & ERR3 & _).
    assert (ART3 : ART RT Σ1 m3).
    { apply (af_frame RT AF Σ1 m2 m3 (usp - 160 - 80) ART2); [rewrite SP1; ul| |exact WM3].
      intros a Ha. apply MU3. cbn [outside]. split; [intros Hin; apply Ha; left; ul|]. split; [| exact I].
      intros Hin. apply Ha. right; left. replace (bv_unsigned a) with TR_INCB by lia. exact IS1. }
    assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 160 - 80)) = usp - 160 - 80) by (apply unsigned_lit; ul).
    apply (VPR Σ1 fds0 fs (Z_to_bv 64 0xf9fac) (Z_to_bv 64 (usp - 160 - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
             (Z_to_bv 64 d) (Z_to_bv 64 FMT_emit) (Z_to_bv 64 (usp - 160 - 80 + 24)) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 owned)
             (Z_to_bv 64 0) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 TR_M2) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m3 so
             (usp - 160 - 80 + 24) lo); try reflexivity; try assumption;
      try (match goal with |- _ - STACK_WIN <= lo => unfold lo, STACK_WIN; lia end).
    + rewrite EU2. reflexivity.
    + destruct Hso as [->|(j & Hj & ->)]; [left; reflexivity| right; exists j; split; [lia| reflexivity]].
    + exact (CLX_io_ssp OUT_rep ERR_rep XENV LIB so m3 CLX3 (AF_DRV Σ1 m3 ART3)).
    + unfold call_ok. rewrite EU2, SP1. split; [exact ST3|]. ul.
    + intros cf3 Hc3.
      destruct (ASTA_unpack RT Σ1 _ _ cf3 Hc3) as (ms3 & (v & m4 & RS3 & (ART4 & MI4 & WM4 & ST4) & PRES4 & OUT4 & ERRP4) & Hc3').
      destruct RS3 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F4 & fc4 & ->).
      rewrite EU2 in ST4, PRES4.
      rewrite (ret_pc_even 0xf9fac) in Hc3' by lia.
      assert (CLX4 : CLX OUT_rep ERR_rep XENV LIB (emit0_next so) m4)
        by exact (CLX_io OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                    _ _ m3 m4 _ _ _ CLX3 PRES4 WM4 OUT4 (ERRP4 ERR3)).
      pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES4 ltac:(intros x Hx; apply IO_outside_hi; ul)) as AG4.
      assert (EF1' : rw_cells asegs m4 (usp - 160 - 80) [C8 (Z_to_bv 64 (usp - 160 - 80 + 24)); C8 (Z_to_bv 64 0xf9ec4); CB 8 junk]).
      { apply (rw_cells_agree asegs m3 m4 _ _ EF1); [| exact WM4]. eapply agree_sub; [exact AG4|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (EF2' : rw_cells asegs m4 (usp - 160 - 80 + 24) [C8 (Z_to_bv 64 0)]).
      { apply (rw_cells_agree asegs m3 m4 _ _ EF2); [| exact WM4]. eapply agree_sub; [exact AG4|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (EF3' : rw_cells asegs m4 (usp - 160 - 80 + 32) [C8 a2'; C8 a3'; C8 a4'; C8 a5'; C8 a6'; C8 a7']).
      { apply (rw_cells_agree asegs m3 m4 _ _ EF3); [| exact WM4]. eapply agree_sub; [exact AG4|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      pose proof (tr_emit_ret_walk (usp - 160) k gp u0 u1 u2 (Z_to_bv 64 plen) (Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7
                    (Z_to_bv 64 owned) (Z_to_bv 64 0) (Z_to_bv 64 TR_M2) s8 s9 s10 s11 u3 u4 u5 u6 a2' a3' a4' a5' a6' a7'
                    F4 fc4 m4 lo junk ST4 ltac:(ul) ltac:(ul)
                    ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia)
                    ltac:(ul) ltac:(lia) EF1' EF2' EF3' MI4) as W3.
      lazymatch type of W3 with evt asegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W3') Hc3').
      intros cf4 Hc4. apply Hk.
      destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & (Hcase & ST5) & Hc4').
      assert (AG04 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m4).
      { apply (agree_trans _ m m1 m4); [| apply (agree_trans _ m1 m2 m4); [| apply (agree_trans _ m2 m3 m4)]].
        - eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. ul.
        - eapply agree_sub; [exact AGS2|]. intros x Hx. cbv beta in *. lia.
        - apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn. split; [lia|]. split; [ul| exact I].
        - eapply agree_sub; [exact AG4|]. intros x Hx. cbv beta in *. lia. }
      assert (AGD04 : agree_on (fun x => d <= x < d + plen) m m4).
      { destruct (Z.eq_dec plen 0) as [Z0|NZ]; [intros a Ha; lia|].
        assert (IN : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
        assert (Ed : d = owned) by exact (P1 ltac:(lia)).
        apply (agree_trans _ m m1 m4); [| apply (agree_trans _ m1 m2 m4); [| apply (agree_trans _ m2 m3 m4)]].
        - eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. pose proof (DOUT x Hx). lia.
        - apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2). intros x Hx. pose proof (DOUT x Hx) as (DO1 & DO2).
          split; [right; right; left; exists owned, plen; split; [exact IN| lia]|].
          apply outside_of_not_in_ranges'. intros Hin. pose proof (client_static_range _ (proj1 (LIB_img _ Hin))). lia.
        - apply (agree_of_munch _ _ _ _ MU3). intros x Hx. pose proof (DOUT x Hx). cbn. split; [ul|]. split; [lia| exact I].
        - apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES4). intros x Hx. pose proof (DOUT x Hx) as (DO1 & DO2). rewrite LV1.
          split; [right; right; left; exists owned, plen; split; [exact IN| lia]|].
          apply outside_of_not_in_ranges'. intros Hin. pose proof (client_static_range _ (proj1 (IO_img _ Hin))). lia. }
      assert (HT4 : TCTX RT OUT_rep ERR_rep XENV LIB Σ1 (emit0_next so) usp buf cap plen d owned payload
                      c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m4).
      { apply (TCTX_agree_nw RT OUT_rep ERR_rep XENV LIB AF Σ Σ1 so (emit0_next so) usp buf cap plen d owned payload
                 c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m m4 HT ART4 MI4); try reflexivity; try assumption; rewrite ?SP1; assumption. }
      destruct Hcase as [(K1 & ->)|(K1 & ->)].
      * left. split; [exact K1|].
        exists Σ1, plen, d, owned, payload, (Z_to_bv 64 0xf9ec4), gp, u0, u1, u2, v, b1, b2, b3, b4, b5, b6, b7, (Z_to_bv 64 TR_M1), s8, s9, s10, s11.
        exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F4, fc4, m4.
        split; [exact Hc4'|]. split; [exact HT4|]. split; [lia|]. unfold FUZZ_COST in *. nia.
      * right. split; [exact K1|].
        exists Σ1, plen, d, owned, payload, gp, u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, (Z_to_bv 64 TR_M1), s8, s9, s10, s11.
        exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F4, fc4, m4.
        split; [exact Hc4'| exact HT4].
Qed.

End Tr2.
