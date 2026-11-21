(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (dir_cpsE's recorded proof replaced by the plain proof of the same lemma in leptonica/kernel_fuzzer, at this binary's addresses, over the stack floor lo := rt_sp0 - STACK_SPAN, the span the start state guarantees writable). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_frmkit D_iface D_defs D_kit D_libiface D_clx D_usage D_open D_read D_rlkit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_D_dir () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface:errno_cellC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K53A236D_defs4TP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs7ERRNO_AC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K53A238RT_iface=client_staticC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib2K53A235D_clxCclient_static_introC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic2or00c69OSSVerify5KrLib2K53A235D_dir7errno_AC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib2K54Spec4Prog6argv_ZC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib2K54Spec5Canon:open_classC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs6OPENEDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs4EXITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC69OSSVerify5KrLib2K53A238RT_iface4PMfdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6ret_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs6path_bC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib6NodesA8open_entC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K54Spec5Canon>msg_read_errorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Canon3evwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs9sigma0_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs:path_slackC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib2K53A236D_open;nth1_argv_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_open6oc_dirC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53A238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs8argv_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs:main_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53A238RT_iface9rt_creditC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_open<path_b_factsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List9app_nil_rC69OSSVerify5KrLib2K54Spec5Stdio6so_bufC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_read;opened_walkC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53A238RT_iface7fp_case03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs8asta_evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface>PMfd_fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs?PMfd_mat_stableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC69OSSVerify5KrLib2K53A238RT_iface5mcostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9sec_bytesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53A238RT_iface7call_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indC69OSSVerify5KrLib2K53A238RT_iface9unwind_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface;malloc_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8rt_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface=af_live_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_clx8CLX_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237D_rlkit@agree_stack_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_read?first_read_walkC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237D_rlkitAchecked_dst_stageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface:rt_pres_fpC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53A235D_clx>CLX_errno_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237D_rlkitCagree_stack_pres_fpC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:length_appC69OSSVerify5KrLib2K53A237D_rlkit:path_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53A236D_defs:drv_constsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs<stderr_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6io_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53A235D_kit@agree_of_pres_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_kit>ro_cells_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_read=read_err_walkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6fp_fmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6fp_argC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6fp_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface;checked_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237D_rlkitAchecked_src_stackC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C69OSSVerify5KrLib2K53A238RT_iface9in_rangesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs8drv_cellC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_open<failed_walk2C1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC69OSSVerify5KrLib2K53A238RT_iface8so_linesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_clxIoutside_of_not_in_ranges'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_clx>io_ssp_pres_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS<cps_realizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:t_emit_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K52AS8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS4cpsEC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs7MAINCTXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs3CLXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6fp_msgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs;ASTA_unpackC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib2K53A238RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7rt_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI69OSSVerify5KrLib2K54Spec5Canon6oclass00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K54Spec5Canon6oclass02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C69OSSVerify5KrLib2K53A238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs:CREDIT_DRVC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib2K53A238RT_iface8e_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8RT_STACKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9ALLOC_RASC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6e_readC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237D_iface9SSP_GUARDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236Layout<g_read_stageC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC69OSSVerify5KrLib2K53A237D_iface7GOT_SSPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs<GOT_LLVMINITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs7S_SHORTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs6S_OVERC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9e_fprintfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237D_iface6e_exitC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53A236D_defs4fds0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs8RET_OPENC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06C69OSSVerify5KrLib2K53A238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathK47Corelib4Init9Datatypes:comparison02K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53A238RT_iface8LIVE_MAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9SEC_BYTESC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A235D_dir<errno_staticC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib2K53A238RT_iface;STDERR_FILEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface>FMT_read_errorC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K54Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:D_libiface6LIB_FPC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section Dir.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract RT.
Hypothesis RDIR : read_icontract_dir RT.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis VARGV : valid_argv argvb.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.

Lemma errno_A : errno_cell (Z_to_bv 64 TP_A) = ERRNO_A.
Proof.
ltac2:(KReplay.run1 (kr_t_D_dir ()) ["Dir"] "h02Hah16__sat1h27__arithh34__ffh46__sat0h58__varmaph65__with71zp;1p;2p;3p;4p;7p;6p10000p4p70R0p1000`p4p710R1p8P0p1001<p4p710p8P0p1001Zp4p7210p8p10027p4p710R0g002TR2p4p710R3p8p10032p4p70R4P1p8P4P0p8P4p1003`p4p710p8p1004=p4p7210R4P1p8P4P3p8g004ij10Tg005Nj11Tg0063j13Tg006Qj2<Tg006nj35Tg007Hj26Tg007bj1CTg008@j2;Tg008fj2@Tg009Pj2?Tg00:8j28Tg00:Tj24Tg00;0j2RTg00;Mj3QTg00<1j2PTg00<Rj1OTg00=2j1NTg00=Rj1KTg00>0j1ETg00>Nj1DTg00?9j27Tg00?\j49Tg00@Gj3BTg00@jj7ATg00ANj2FTg00B0j2GTg00B\j3HTg00C;j4ITg00Cmj2JTg00DHj2>TP2j6LTg00EGj1MTg00FFj7=Tf0R2#1#1p=2f1R3g00FjR4g00GIR1P1g00GiR0P2g00HIF=p=:g00HiR5g00IGR6#0#0#1#0#0#1#2#0#0#1#0#0#0#1#2#0#0#1#2#3R7%16R6#0#2#0#2#3R8,<21<78R8555X751658%16#2#2R8#CR91;97'@%36R6%38R8'?g00IlR:/86R;14:81R68R<,8:[R=[14:6R>g00JJR?AQ683UW014:<\?^0>P3g00Jf1P:6'6P;eO1P=g00KLR=#O%N=%K5%E5%D5R=P4P1P1P0P5175:g00L81757R1C9,:=P5P1g00L_1756=B59C9,:=FA1F=0P2f2R=g00MFR0g00MfR6'61G2==506dAH5:3CIb3b5b614:7187<'JP2b2b1b4b1,>7ELg00NF,;9#Mg00O=555eo"). Qed.

Lemma errno_static : forall i, 0 <= i < 4 -> client_static (errno_cell (Z_to_bv 64 TP_A) + i).
Proof.
ltac2:(KReplay.run1 (kr_t_D_dir ()) ["Dir"] "h04__p1h14__p2h24__x1h32Hih47__arithh54__ffh68__varmaph75__with81ih91zp;1p;2p;3p;8p;4p;6p;7g005Nj10Tg0063j1QTg00:8j2GTg00P7j2LTg00PTj1tTg00<Rj1fTg00=2j1cTg00QVj2aTg00>0j1`Tg00>Nj1^Tg00?9j2HTg00R4j2[Tg00RWj1sTg004ij11Tg00S9j3_Tg00S\j3]Tg00T?j8rTg00ANj2qTg007Hj2pTg00B0j2oTg006nj3nTg00B\j3mTg00C;j4lTg006Qj2kTg00Tcj2gTg007bj1hTg008@j2dTg00EGj1iTg002Tj6jTg00:Tj2TTg00Cmj2UTg00?\j4KTg00FFj7PTg00@jj7STg00Uhj6bTg00VLj7OTg00W0j2MTf2R0f1R1'Tf0R2'Up=Ig00HiR3P1g00L8R4P2CKp=wP0g00FjR5g00GIR6P6g00GiR7P3P1g00L_1H32CKg00HIR8FPp=4f3R9P5P6P6P7P0P5P6P6P7P1P8FPP2FSp=WP1P5P6P6P7P2Ebp=V%02#0#0#0#1#0p=6%12#1#0#0#0#0#0#1p==%02#1#0#0p=>%02#0#0#Qp=3%12#1#0#1#1#0#0p=7%02#1#1#0p=B%12#1#1#0p=D%02#0#1#1p=81H32p=R%02#0p=@%12#0#0#Qp=<P31H31P4P2CKp=\%02#1#0#1p=:%12#0#0#0p=E%12#1#0#0p=J%12#1#0#0#0#0#1#0p=F%02#0#0#0p=9%02#0#0#1p=N%12#0#0#1p=A%02#0#1#0#1#1#0#0p=?%12#0#1#1p=C%12#1#0p=v%12#0#1#0p=Z%02#0#1#0p=Y%02#1p=X%12#1p=;f6P5P6P6P7f5P5P6P6P7f4R:P5P6P6P7P31H39P4P0CKP8FPP1FSP2FOp=5P:P5P6P6P7P9P0P5P6P6P7P1P2FOFOp=u1T:91G01'U/M2p=21M12,M0p=eg00IlR8g00IGR4#0R;#0R<#QR=,G27I2R>P3g00O=R?1L20#tX931L?1R?p-0R@g00KLRA#f%cA1a31%`3%^3RAP5P6P6P7PAPA1H381[34R5'wA4A5=CW%s6PA1VA9PAPAPA%64#=#>#3R6%74#B#D#8#3R=#R%1;#@#<R;#R5_3=]35R5'\%64#=#:#3RB94A5CWPAPAPA%64#=#E#3RCP5%64#=#E#<RD94A5PAPAPA%64#=#J#3REP5%64#=#J#<RF94A5PAPAPA%64#F#9#3RGP5%64#F#N#3RH94A5PAPAPA%64#F#>#3RIP5%64#F#:#3RJ94A5PAPAPA%64#F#E#3RKP5%64#F#A#3RL94A5PAPAPA%@4#?#?#3RMP5%@4#?#?#<RN94A5PAPAPA%@4#?#8#9#3ROP5%@4#?#8#9#<RP94A5PAPAPA%@4#?#8#>#3RQP5%@4#?#8#>#<RR94A5PAPAPA%@4#?#8#E#3RSP5%@4#:#A#A#C#3RT94A5PAPAPA%v4#Z#:#8#Y#3RUP5%74#:#8#J#<RV94A5PAPAPA%74#:#>#9#3RWP5%74#:#>#9#<RX94A5PAPAPA%74#:#>#>#3RYP5%14#C#N#C#X#E#3RZ94A5PAPAPA%14#C#N#C#X#A#3R[P5%74#B#D#Y#3R\94A5PAPAPA%74#B#D#>#3R]P5%74#B#D#B#3R^94A5PAPAPA%74#B#D#E#3R_P5%74#B#D#A#3R`94A5PAPAPA%74#B#D#C#3RaP5%14#=#;#8#C#3Rb94A5PAPAPA%14#=#;#8#J#3RcP5%14#;#9#A#:#E#3Rd94A51VA:F5F5F5F5F5F5F5F5F5F5F5F5F5F5F5F5F5DuGr1qA7P2P0g00MFRAg00MfR7'p1o20=nA7dAm381Clb5b6b7X23X0@W11k=;R;/L1R=1G=B5I6PCP=P=PDPEP=P=PFPGP=P=PHPIP=P=PJPKP=P=PLPMP=P=PNPOP=P=PPPQP=P=PRPSP=P=PTPUP=P=PVPWP=P=PXPYP=P=PZP[P=P=P\P]P=P=P^P_P=P=P`PaP=P=PbPcP=P=PdP9D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D25e0\>^23^0@^1@P2%14#;#9#A#:#A#3R21L;0R;%14#;#9#A#;#;#;#;#3R@,G;3I%64#C#J#Z#3R>%64#=#9#<R4,G;7I;P0P1O4b4P>P?P?P4P6P?P?PBPCP?P?PDPEP?P?PFPGP?P?PHPIP?P?PJPKP?P?PLPMP?P?PNPOP?P?PPPQP?P?PRPSP?P?PTPUP?P?PVPWP?P?PXPYP?P?PZP[P?P?P\P]P?P?P^P_P?P?P`PaP?P?PbPcP?P?Pd1G?@9I2?D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2e'g%9<#hg00NF'd#ig00WJEjW3X83o"). Qed.

Theorem dir_cpsE : Z.of_nat (length argvb) = 2 -> open_class (nth 1 (argv_Z argvb) []) fs = OCDir ->
  cpsE asegs (OPENED RT OUT_rep ERR_rep XENV LIB argvb fs) (evw 2 (msg_read_error (nth 1 (argv_Z argvb) []))) (EXIT fs 2).
Proof using AF AF_DRV MAL RDIR FPR EXC VARGV OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros HL HCL T c HO Hk.
  destruct HO as (Σ & usp & ap & path & gp & s1 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7
                  & m & ent & HA & HCTX & HSIG & HB & Hap & Hhi & HENT & HSLK).
  rewrite nth1_argv_Z in HCL. pose proof (oc_dir _ _ HCL) as HD. unfold path_b in HENT. rewrite HD in HENT.
  injection HENT as <-.
  pose proof HCTX as (ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof HSIG as (LV & FRS & CR & USP0' & SPW).
  destruct (path_b_facts argvb VARGV HL) as (NZ & NSL & NDD & LEN).
  set (lo := rt_sp0 RT Σ - STACK_SPAN) in *.
  set (F1 := fd_insert fds0 (Z_to_bv 64 3) FdDir) in *.
  rewrite nth1_argv_Z.
  replace (evw 2 (msg_read_error (map bv_unsigned (nth 1 argvb []))))
    with (evw 2 (fp_msg (FPread_error path (path_b argvb))) ++ evw 1 (so_buf stdout_init))
    by (cbn [fp_msg so_buf stdout_init]; rewrite app_nil_r; reflexivity).
  (* [comment removed for export] *)
  destruct (ASTA_unpack RT Σ _ _ c HA) as (ms0 & RS0 & HA').
  destruct RS0 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & ->).
  rewrite (ret_pc_even RET_OPEN) in HA' by (unfold RET_OPEN; lia).
  pose proof (opened_walk usp gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m MI0) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ F1 fs _ _ W1') HA').
  intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & <- & Hc1').
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  apply (MAL Σ (PMfd F1 fs) (Z_to_bv 64 0xf9680) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
           (Z_to_bv 64 65536) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 (Z_to_bv 64 3) (Z_to_bv 64 65536) s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m 65536 lo); try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - lia.
  - rewrite LV. reflexivity.
  - unfold mcost, CREDIT_DRV in *. cbn. lia.
  - intros _. rewrite LV. cbn [sec_bytes]. unfold SEC_BYTES. lia.   (* [comment removed for export] *)
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - unfold unwind_ok. rewrite EU, !unsigned_lit by lia. split; [cbn; tauto|]. left. ul.
  - intros cf2 (Σ' & p & Hc2 & LV' & FRS' & SP' & CR' & Pp & Pal & Ptop).
    destruct (ASTA_unpack RT Σ' _ _ cf2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2) & Hc2').
    destruct RS2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    rewrite EU in ST2, PRES2.
    pose proof (af_live_range RT AF Σ' m2 p 65536 ART2 ltac:(rewrite LV'; left; reflexivity)) as (PR1 & PR2 & PR3).
    assert (CLX2 : CLX OUT_rep ERR_rep XENV LIB stdout_init m2)
      by exact (CLX_pres OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                  _ m m2 _ _ _ CLX0 PRES2 WM2).
    pose proof (agree_stack_pres _ _ _ _ _ PRES2) as AG2.
    (* [comment removed for export] *)
    pose proof (first_read_walk usp p gp t0' t1' t2' s1 a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path) s3 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6' F' fc' m2 ltac:(ul) MI2) as W2.
    rewrite (ret_pc_even 0xf9680) in Hc2' by lia.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ' F1 fs _ _ W2') Hc2').
    intros cf3 Hc3.
    destruct (ASTA_unpack RT Σ' _ _ cf3 Hc3) as (ms3 & <- & Hc3').
    pose proof CLX2 as (_ & _ & _ & _ & _ & _ & RS2).
    (* [comment removed for export] *)
    apply (RDIR Σ' F1 fs (Z_to_bv 64 0xf9714) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 2)
             (Z_to_bv 64 p) (Z_to_bv 64 3) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 65536) a3' a4' a5' a6' a7' (Z_to_bv 64 path)
             (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 p) s8 s9 s10 s11
             t3' t4' t5' t6' F' fc' m2 3 g_read_stage 65536 lo); try reflexivity; try assumption.
    + lia.
    + lia.
    + ul.
    + exact (checked_dst_stage RT AF Σ' m2 _ 65536 ART2 RS2 ltac:(lia)).
    + apply errno_static.
    + rewrite errno_A. pose proof CLX2 as (_ & _ & _ & _ & _ & ERRN2 & _). exact ERRN2.
    + unfold call_ok. rewrite EU, SP'. split; [exact ST2|]. ul.
    + intros cf4 Hc4.
      destruct (ASTA_unpack RT Σ' _ _ cf4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4) & Hc4').
      destruct RS4 as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & F'' & fc'' & ->).
      rewrite EU in ST4, PRES4. rewrite errno_A in PRES4.
      destruct (CLX_errno_pres OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                  _ m2 m4 _ _ _ CLX2 PRES4 WM4) as (OUT4 & ERR4 & XE4 & LIB4).
      pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES4 ltac:(intros x Hx; cbn; split; [unfold ERRNO_A, TP_A; ul| exact I])) as AG4.
      assert (HB4 : bytes_at asegs m4 path (path_b argvb ++ [Z_to_bv 8 0])).
      { apply (path_agree m2 m4 usp path); [| lia| rewrite length_app; cbn [length]; ul| exact AG4].
        apply (path_agree m m2 usp path); [exact HB| lia| rewrite length_app; cbn [length]; ul| exact AG2]. }
      assert (HSLK4 : path_slack argvb m4 path).
      { destruct HSLK as (sl & SL & SLM & SLB). exists sl. split; [| split; assumption].
        apply (path_agree m2 m4 usp); [| lia| ul| exact AG4].
        apply (path_agree m m2 usp); [exact SL| lia| ul| exact AG2]. }
      pose proof (AF_DRV Σ' m4 ART4) as (SC4 & _).
      assert (SSP4 : io_ssp m4).
      { pose proof CLX2 as (_ & _ & _ & _ & (g2 & G2) & _). exists g2. split; [exact (proj1 (proj2 (AF_DRV Σ' m4 ART4)))|].
        apply (ro_cells_agree asegs m2 m4 _ _ G2). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES4). intros x Hx. cbn in Hx.
        split; [right; left; apply client_static_intro; unfold SSP_GUARD in *; lia| cbn; unfold ERRNO_A, TP_A, SSP_GUARD in *; split; [lia| exact I]]. }
      (* [comment removed for export] *)
      pose proof (read_err_walk usp gp t0'' t1'' t2'' (Z_to_bv 64 p) a1'' a2'' a3'' a4'' a5'' a6'' a7'' (Z_to_bv 64 path)
                    (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 p) s8 s9 s10 s11
                    t3'' t4'' t5'' t6'' F'' fc'' m4 SC4 MI4) as W3.
      rewrite (ret_pc_even 0xf9714) in Hc4' by lia.
      lazymatch type of W3 with evt asegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ' F1 fs _ _ W3') Hc4').
      intros cf5 Hc5.
      destruct (ASTA_unpack RT Σ' _ _ cf5 Hc5) as (ms5 & <- & Hc5').
      eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
      apply (FPR Σ' F1 fs (Z_to_bv 64 0xf9894) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0'' t1'' t2'' (Z_to_bv 64 2)
               (Z_to_bv 64 p) (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 FMT_read_error) (Z_to_bv 64 path) a3'' a4'' a5'' a6'' a7''
               (Z_to_bv 64 path) (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 p)
               s8 s9 s10 s11 t3'' t4'' t5'' t6'' F'' fc'' m4 (FPread_error path (path_b argvb)) STDERR_FILE lo);
        try reflexivity; try assumption.
      * intros a s Hs. cbn [fp_str] in Hs. injection Hs as <- <-. split; [exact HB4|]. split; [exact NZ|].
        split; [lia|]. split; [apply (checked_src_stack RT AF Σ' m4); [exact ART4| rewrite SP'; ul| ul| rewrite EU; lia]|].
        split; [rewrite EU; lia| exact HSLK4].
      * unfold call_ok. rewrite EU, SP'. split; [exact ST4|]. ul.
      * intros cf6 Hc6.
        destruct (ASTA_unpack RT Σ' _ _ cf6 Hc6) as (ms6 & (v & m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ERR6 & OUTP6) & Hc6').
        destruct RS6 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F6 & fc6 & ->).
        rewrite EU in ST6, PRES6.
        pose proof (OUTP6 stdout_init OUT4) as OUT6.
        assert (XE6 : XENV m6).
        { apply (XENV_loc m4 m6 XE4). intros a Ha. apply PRES6; [right; left; exact (proj1 (XENV_img _ Ha))|].
          exact (proj1 (proj2 (proj2 (XENV_img _ Ha)))). }
        (* [comment removed for export] *)
        pose proof (failed_walk2 usp gp (Z_to_bv 64 p) (Z_to_bv 64 path) (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536)
                      (Z_to_bv 64 g_read_stage) (Z_to_bv 64 p) s8 s9 s10 s11 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6
                      F6 fc6 m6 MI6) as W4.
        rewrite (ret_pc_even 0xf9894) in Hc6' by lia.
        lazymatch type of W4 with evt asegs _ ?X =>
          assert (W4' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W4) end.
        clear W4.
        apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ' F1 fs _ _ W4') Hc6').
        intros cf7 Hc7.
        destruct (ASTA_unpack RT Σ' _ _ cf7 Hc7) as (ms7 & <- & Hc7').
        apply (EXC Σ' F1 fs (Z_to_bv 64 0xf98c0) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 2)
                 (Z_to_bv 64 p) (Z_to_bv 64 2) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 path) (Z_to_bv 64 0) (Z_to_bv 64 3)
                 (Z_to_bv 64 65536) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 p) s8 s9 s10 s11 u3 u4 u5 u6 F6 fc6
                 m6 stdout_init 2 lo); try reflexivity; try assumption.
        -- lia.
        -- left. reflexivity.
        -- unfold call_ok. rewrite EU, SP'. split; [exact ST6|]. ul.
        -- eapply (io_ssp_pres_fp IO_FP _ _ _ m4 m6); [| exact SSP4| exact (AF_DRV _ _ ART6)| exact PRES6].
           intros x Hx. apply outside_of_not_in_ranges'. intros Hin. apply (proj1 (proj2 (IO_img x Hin))). unfold drv_cell. right; left; exact Hx.
Qed.

End Dir.
