(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import Stdio_kit Stdio_kitI F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import F_pop_arg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import Printf_zfacts F_printf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require F_printf_core_exit F_printf_core_end F_printf_core_exit1 F_printf_core_scan F_printf_core_flags F_printf_core_width F_printf_core_prec F_printf_core_state F_printf_core_dir F_printf_core_t6 F_printf_core_t5 F_printf_core_t4 F_printf_core_t3 F_printf_core_t2 F_printf_core_t1 F_printf_core_tail F_printf_core_intc2 F_printf_core_intc F_printf_core_dloop F_printf_core_fmtu2 F_printf_core_fmtu F_printf_core_cvd F_printf_core_cvu F_printf_core_xloop F_printf_core_cvx F_printf_core_cvs F_printf_core_cvfp F_printf_core_conv F_printf_core_head F_printf_core_p1 F_printf_core_pro.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Export F_printf_core_common.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_printf_core () := "C5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC5ARocqVerifyHarness?AgentSubmission5BothWBF_printf_core_exit6L_EXITC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface?sink_frame_stmtC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF5postFC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model4mpadC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common4POSTC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission5BothWAF_printf_core_end5L_ENDc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core6L_EXITC5ARocqVerifyHarness?AgentSubmission5BothWCF_printf_core_exit17L_EXIT1C5ARocqVerifyHarness?AgentSubmission5BothWBF_printf_core_scan6L_SCANC5ARocqVerifyHarness?AgentSubmission5BothWCF_printf_core_flags7L_FLAGSC5ARocqVerifyHarness?AgentSubmission5BothWCF_printf_core_width7L_WLOOPC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common7S_WLOOPC5ARocqVerifyHarness?AgentSubmission5BothWCF_printf_core_width7L_WIDTHC5ARocqVerifyHarness?AgentSubmission5BothWBF_printf_core_prec7L_PLOOPC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common7S_PLOOPC5ARocqVerifyHarness?AgentSubmission5BothWBF_printf_core_prec6L_PRECC5ARocqVerifyHarness?AgentSubmission5BothWCF_printf_core_state7L_STATEc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_WIDTHc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core6L_PRECC5ARocqVerifyHarness?AgentSubmission5BothWAF_printf_core_dir5L_DIRc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_FLAGSc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_WLOOPc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_PLOOPc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_STATEC5ARocqVerifyHarness?AgentSubmission5BothW@F_printf_core_t64L_T6C5ARocqVerifyHarness?AgentSubmission5BothW@F_printf_core_t54L_T5c5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core4L_T6C5ARocqVerifyHarness?AgentSubmission5BothW@F_printf_core_t44L_T4c5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core4L_T5C5ARocqVerifyHarness?AgentSubmission5BothW@F_printf_core_t34L_T3c5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core4L_T4C5ARocqVerifyHarness?AgentSubmission5BothW@F_printf_core_t24L_T2c5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core4L_T3C5ARocqVerifyHarness?AgentSubmission5BothW@F_printf_core_t14L_T1c5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core4L_T2C5ARocqVerifyHarness?AgentSubmission5BothWBF_printf_core_tail6L_TAILc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core4L_T1C5ARocqVerifyHarness?AgentSubmission5BothWCF_printf_core_intc27L_INTC2c5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core6L_TAILC5ARocqVerifyHarness?AgentSubmission5BothWBF_printf_core_intc6L_INTCc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_INTC2C5ARocqVerifyHarness?AgentSubmission5BothWCF_printf_core_dloop7L_DLOOPC5ARocqVerifyHarness?AgentSubmission5BothWCF_printf_core_fmtu27L_FMTU2c5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core6L_INTCC5ARocqVerifyHarness?AgentSubmission5BothWBF_printf_core_fmtu6L_FMTUc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_FMTU2c5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_DLOOPC5ARocqVerifyHarness?AgentSubmission5BothWAF_printf_core_cvd6L_CV_Dc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core6L_FMTUC5ARocqVerifyHarness?AgentSubmission5BothWAF_printf_core_cvu6L_CV_UC5ARocqVerifyHarness?AgentSubmission5BothWCF_printf_core_xloop7L_XLOOPC5ARocqVerifyHarness?AgentSubmission5BothWAF_printf_core_cvx6L_CV_Xc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_XLOOPC5ARocqVerifyHarness?AgentSubmission5BothWAF_printf_core_cvs6L_CV_SC5ARocqVerifyHarness?AgentSubmission5BothWBF_printf_core_cvfp7L_CV_FPC5ARocqVerifyHarness?AgentSubmission5BothWBF_printf_core_conv6L_CONVc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core6L_CV_Dc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core6L_CV_Uc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core6L_CV_Xc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core6L_CV_Sc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_CV_FPC5ARocqVerifyHarness?AgentSubmission5BothWBF_printf_core_head6L_HEADI47Corelib4Init9Datatypes3nat00c5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core6L_SCANc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core5L_DIRc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core6L_CONVc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core5L_ENDC5ARocqVerifyHarness?AgentSubmission5BothW@F_printf_core_p14L_P1c5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_EXIT1C5ARocqVerifyHarness?AgentSubmission5BothWAF_printf_core_pro5L_PROK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common7ctx_allC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_lib2zbC5ARocqVerifyHarness?AgentSubmission5BothW9F_pop_arg7va_areaC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles9ssp_cellsK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface7args_okI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface;fpcall_stmtC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model8fp_callsI47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common5S_PROC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common4finvK47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common8lo_cellsK47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common1WC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common8hi_cellsC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common6S_HEADK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics5Riscv7Prelude4tree00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common8Fok_reflC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common<implAM_eq_msC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF?implAM_from_evtC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model<printf_modelC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model;printf_loopC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF6implAMK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls7got_sspC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9ssp_guardK47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission6Common<Printf_model4parg00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C5ARocqVerifyHarness?AgentSubmission6Common5FmtFp7INT_MAXC5ARocqVerifyHarness?AgentSubmission6Common<Printf_model8pass1_okC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common5POST1C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common4S_P1C47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF7evtF_eqK46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic5False00c5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_CORE2C5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface?sink_flags_stmtC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface:topok_stmtC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface8out_stmtC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0C5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6ashenvC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5inregC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface@printf_core_postC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC47Corelib4Init5Logic5proj1K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05I47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics5Riscv3Sem7reg_getC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common3FokC5ARocqVerifyHarness?AgentSubmission5BothW6MonadF;implAM_monoC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface@printf_core_stmtK47Corelib4Init5Logic2ex01I5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission5BothW=Strnlen_iface>strnlen_a_stmtC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface8PC_DEPTHC5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles;GLOBALS_TOPC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface<STATIC_SPLITC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHI47Corelib4Init9Datatypes:comparison00c5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_coreAprintf_core_proofC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_ifaceAprintf_core1_postc5ARocqVerifyHarness?AgentSubmission5BothW=F_printf_core7L_CORE1C5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_nilC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_monoC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_ifaceAprintf_core1_stmt".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Local Ltac acc_hint ::= lazymatch goal with |- acc_in _ (wa ?e, ?n) => change (wa e) with (Z_to_bv 64 e : word); solve_acc1 end.
  Local Ltac acc_enrich ::=
    repeat match goal with
    | H : nth_error ?l ?k = Some ?x |- _ =>
        lazymatch goal with _ : (k < length l)%nat |- _ => fail | _ => pose proof (nth_error_some_bound l k x H) end
    end;
    rewrite ?u32s_length, ?u64s_length, ?length_app, ?repeat_length, ?zb_length in *; cbn [length] in *; unfold zlength in *.
  Context {St : Type}.
  Variables (Fp B BS : Z) (RB : region) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS RB SINK TOPOK OUT.
  Hypothesis HSTRN : strnlen_a_stmt.
  Variables (RNG : footprint) (rstk rfmt : region).
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q < 2^47)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (A + zlength fmt <= 724992)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((737200 <= Fp /\ Fp + 232 <= 762616) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((6345432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  Hypothesis KH : (KHIGH <= lo)%Z.
  Hypothesis RSK : (r_lo rstk <= lo /\ q <= r_hi rstk)%Z.
  Hypothesis RFM : inreg rfmt A (zlength fmt).
  Hypothesis RPF : inreg rfmt 68436 9.
  Hypothesis RBI : inreg RB B BS.
  Hypothesis RG_stk : rng RNG lo (q - lo).
  Hypothesis RG_img : rng_aimg RNG.
  Hypothesis RG_ap : rng RNG AP 8.
  Hypothesis RG_va : rng RNG VA (8 * zlength slots).
  Hypothesis RG_F : rng RNG Fp 232.
  Hypothesis RG_B : rng RNG B BS.
  Hypothesis RG_fmt : rng RNG A (zlength fmt).
  Hypothesis RR_stk : rrng RNG rstk.
  Hypothesis RR_fmt : rrng RNG rfmt.
  Hypothesis RR_B : rrng RNG RB.
  Hypothesis ENV0 : ashenv m0.
  Hypothesis RC_stk : rclean m0 rstk.
  Hypothesis RC_fmt : rclean m0 rfmt.
  Hypothesis RC_B : rclean m0 RB.

  (* [comment removed for export] *)
  Local Notation ctx_all := (F_printf_core_common.ctx_all RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation appW_W := (F_printf_core_common.appW_W Fp B BS RB q m0 lo AP VA LO SEP_F HAP KH RBI RC_B).
  Local Notation ashsafe_W := (F_printf_core_common.ashsafe_W Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP KH).
  Local Notation env_now := (F_printf_core_common.env_now Fp B BS q m0 lo AP VA LO GLO SEP_F SEP_B HAP KH ENV0).
  Local Notation rc_now := (F_printf_core_common.rc_now Fp B BS RB q m0 lo AP VA LO SEP_F HAP KH RBI RC_B).
  Local Notation arg_ok_s_W := (F_printf_core_common.arg_ok_s_W Fp B BS RNG q lo fmt AP slots).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  (* [comment removed for export] *)
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS RB RNG q m0 lo fmt AP VA slots LO SEP_F HAP KH RBI RC_B).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS RB RNG q m0 lo fmt AP VA slots LO SEP_F HAP KH RBI RC_B).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq RNG q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA RG_stk RG_img RG_ap RG_va).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq Fp B BS RB HSTRN RNG q gp tp m0 lo AP VA LO GLO QHI SEP_F SEP_B HAP KH RBI RG_stk RG_img ENV0 RC_B).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS RB SINK TOPOK OUT TOK HOUT RNG q gp tp m0 lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS RB SINK TOPOK OUTFP TOK RNG q gp tp m0 lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS RB SINK RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS RB SINK RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS RB SINK TOPOK OUTFP RNG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
  (* [comment removed for export] *)
  Ltac len_norm := unfold zlength, zrepeat; rewrite ?repeat_length, ?zb_length, ?length_map, ?length_firstn, ?length_skipn, ?length_app; cbn [length]; try rewrite !Z2Nat.id by lia.
  Ltac inreg_side := solve [ unfold inreg in *; len_norm; unfold zlength in *; lia ].
  Ltac rng_side :=
    lazymatch goal with |- rng ?RNG0 ?lo' ?len' =>
      first [ assumption
            | match goal with H : rng RNG0 ?lo ?len |- _ => apply (rng_sub' RNG0 lo len lo' len' H); solve [len_norm; unfold zlength in *; lia] end ]
    end.
  Ltac body_reg_stk := exists rstk; split; [ exact RC_stk | split; [ inreg_side | exact RR_stk ] ].
  Ltac hypMU := match goal with H : munch _ m0 _ |- _ => exact H end.
  Ltac hypWM := match goal with H : wmono _ m0 _ |- _ => exact H end.
  (* [comment removed for export] *)
  Ltac memset_pad PADa :=
    eapply (memset_callZ RNG (r_lo rstk) (r_hi rstk) (r_rlo rstk) (r_rhi rstk));
    [ exact PADa | match goal with H : mem_inv _ _ |- _ => exact H end | lia | lia | lia | lia
    | match goal with H : stk _ _ _ _ |- _ => exact H end | lia | exact KH
    | eapply env_now; [ hypMU | hypWM ]
    | apply rclean_shclean; eapply rc_now; [ exact RC_stk | hypMU | hypWM ]
    | lia | lia | lia | lia | exact RG_img | rng_side | rng_side | exact RR_stk ].
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
    unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
    try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
         lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
    try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
         lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
    unfold zlength in *; hush.
  Ltac hyp :=
    lazymatch goal with
    | |- rw_cells _ ?m ?A ?cs =>
        match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
    | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
    end.
  Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
  Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
  Ltac rd_fmt idx :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evtF_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
    eapply implAM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  (* [comment removed for export] *)
  Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
    end.
  Local Ltac transport_call_extra segs W m m' MU WM ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ eapply (sink_call W m m' st) in H;
                [ | exact MU | exact WM
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    end.
  Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
  Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
  Local Ltac mem_after_store ::= mem_after_store_fast.
  Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
  Local Ltac lia ::= lia3.
  Ltac out_call_with r :=
    ileave; eapply implAM_bind;
    [ eapply (out_callq r);
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 732688 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 6214544 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | |
      | hypMU | hypWM
      | first [ assumption | idtac ]
      | first [ inreg_side | idtac ]
      | first [ rng_side | idtac ]
      | first [ assumption | idtac ] ]
    | cbv beta ].
  Tactic Notation "out_call" constr(r) := out_call_with r.
  Tactic Notation "out_call" := out_call_with rfmt.
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call bsegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := cbv delta [bsegs bsegs] in *; fold bsegs in *.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    let rb := fresh "rb" in let RCb := fresh "RCb" in let IRb := fresh "IRb" in let RRb := fresh "RRb" in let RGb := fresh "RGb" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & (rb & RCb & IRb & RRb) & RGb & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & PFlo & PFhi & Hi4 & Hfl & HnI & Hnp & Hplp);
    pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
    pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
    let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
  Ltac mk_tinv :=
    lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      unfold tinv, body_loc;
      split; [mk_finv|];
      split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
      split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
      split; [match goal with H : SINK m _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
      split; [lia|];
      split; [assumption|];
      split; [assumption|];
      split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
      split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [first [assumption | reflexivity | lia | zl] |];
      split; [match goal with H : rclean m0 ?r, H2 : inreg ?r _ _, H3 : rrng _ ?r |- _ => exists r; split; [exact H| split; [exact H2| exact H3]] end |];
      split; [assumption|];
      repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
    end.

  (* [comment removed for export] *)
  Lemma L_EXIT : S_EXIT.
Proof using LO RG_stk RG_img.
    first [ apply F_printf_core_exit.L_EXIT; first [eassumption]
          | intros; eapply F_printf_core_exit.L_EXIT; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_END : S_END.
Proof using LO GLO SEP_F HAP VAHI RG_stk RG_img.
    first [ apply F_printf_core_end.L_END; first [eassumption | eexact L_EXIT]
          | intros; eapply F_printf_core_end.L_END; first [eassumption | eexact L_EXIT] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_EXIT1 : S_EXIT1.
Proof using LO RG_stk RG_img.
    first [ apply F_printf_core_exit1.L_EXIT1; first [eassumption]
          | intros; eapply F_printf_core_exit1.L_EXIT1; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_SCAN : S_SCAN.
Proof using HF HA A0 RG_fmt.
    first [ apply F_printf_core_scan.L_SCAN; first [eassumption]
          | intros; eapply F_printf_core_scan.L_SCAN; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_FLAGS : S_FLAGS.
Proof using HF RG_fmt.
    first [ apply F_printf_core_flags.L_FLAGS; first [eassumption]
          | intros; eapply F_printf_core_flags.L_FLAGS; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_WLOOP : S_WLOOP.
Proof using HF LO RG_stk RG_fmt.
    first [ apply F_printf_core_width.L_WLOOP; first [eassumption]
          | intros; eapply F_printf_core_width.L_WLOOP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
Proof using HF.
    first [ intro; apply F_printf_core_width.L_WIDTH; first [eassumption]
          | intros; eapply F_printf_core_width.L_WIDTH; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_PLOOP : S_PLOOP.
Proof using HF LO RG_stk RG_fmt.
    first [ apply F_printf_core_prec.L_PLOOP; first [eassumption]
          | intros; eapply F_printf_core_prec.L_PLOOP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_PREC : S_PLOOP -> S_PREC.
Proof using HF RG_fmt.
    first [ intro; apply F_printf_core_prec.L_PREC; first [eassumption]
          | intros; eapply F_printf_core_prec.L_PREC; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_STATE : S_STATE.
Proof using HF RG_img RG_fmt.
    first [ apply F_printf_core_state.L_STATE; first [eassumption]
          | intros; eapply F_printf_core_state.L_STATE; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_DIR : S_DIR.
Proof using HF LO RG_stk RG_img RG_fmt.
    first [ apply F_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE]
          | intros; eapply F_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T6 : S_T6.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RBI RG_stk RG_img RG_F RG_B RR_stk RR_B ENV0 RC_stk RC_B.
    first [ apply F_printf_core_t6.L_T6; first [eassumption]
          | intros; eapply F_printf_core_t6.L_T6; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T5 : S_T5.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RBI RG_stk RG_img RG_F RG_B RR_stk RR_B ENV0 RC_stk RC_B.
    first [ apply F_printf_core_t5.L_T5; first [eassumption | eexact L_T6]
          | intros; eapply F_printf_core_t5.L_T5; first [eassumption | eexact L_T6] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T4 : S_T4.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RBI RG_stk RG_img RG_F RG_B RR_stk RR_B ENV0 RC_stk RC_B.
    first [ apply F_printf_core_t4.L_T4; first [eassumption | eexact L_T5]
          | intros; eapply F_printf_core_t4.L_T4; first [eassumption | eexact L_T5] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T3 : S_T3.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RBI RG_stk RG_img RG_F RG_B RR_stk RR_B ENV0 RC_stk RC_B.
    first [ apply F_printf_core_t3.L_T3; first [eassumption | eexact L_T4]
          | intros; eapply F_printf_core_t3.L_T3; first [eassumption | eexact L_T4] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T2 : S_T2.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RPF RBI RG_stk RG_img RG_F RG_B RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ apply F_printf_core_t2.L_T2; first [eassumption | eexact L_T3]
          | intros; eapply F_printf_core_t2.L_T2; first [eassumption | eexact L_T3] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T1 : S_T1.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RPF RBI RG_stk RG_img RG_F RG_B RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ apply F_printf_core_t1.L_T1; first [eassumption | eexact L_T2]
          | intros; eapply F_printf_core_t1.L_T1; first [eassumption | eexact L_T2] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_TAIL : S_TAIL.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RPF RBI RG_stk RG_img RG_F RG_B RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ apply F_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
          | intros; eapply F_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_INTC2 : S_INTC2.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RPF RBI RG_stk RG_img RG_F RG_B RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ apply F_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL]
          | intros; eapply F_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_INTC : S_INTC.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RPF RBI RG_stk RG_img RG_F RG_B RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ apply F_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2]
          | intros; eapply F_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_DLOOP : S_DLOOP.
Proof using LO GLO QHI RG_stk.
    first [ apply F_printf_core_dloop.L_DLOOP; first [eassumption]
          | intros; eapply F_printf_core_dloop.L_DLOOP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_FMTU2 : S_FMTU2.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RPF RBI RG_stk RG_img RG_F RG_B RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ apply F_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC]
          | intros; eapply F_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_FMTU : S_FMTU.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RPF RBI RG_stk RG_img RG_F RG_B RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ apply F_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
          | intros; eapply F_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_D : S_CV_D.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RPF RBI RG_stk RG_img RG_F RG_B RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ apply F_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU]
          | intros; eapply F_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_U : S_CV_U.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RPF RBI RG_stk RG_img RG_F RG_B RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ apply F_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU]
          | intros; eapply F_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_XLOOP : S_XLOOP.
Proof using LO GLO QHI RG_stk RG_img.
    first [ apply F_printf_core_xloop.L_XLOOP; first [eassumption]
          | intros; eapply F_printf_core_xloop.L_XLOOP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_X : S_CV_X.
Proof using SFR SFL TOK HOUT LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RPF RBI RG_stk RG_img RG_F RG_B RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ apply F_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
          | intros; eapply F_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_S : S_CV_S.
Proof using SFR SFL TOK HOUT HSTRN LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RSK RPF RBI RG_stk RG_img RG_F RG_B RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ apply F_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL]
          | intros; eapply F_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_FP : S_CV_FP.
Proof using TOK LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B.
    first [ apply F_printf_core_cvfp.L_CV_FP; first [eassumption]
          | intros; eapply F_printf_core_cvfp.L_CV_FP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CONV : S_CONV.
Proof using SFR SFL TOK HOUT HSTRN HF LO GLO QHI TQ HA SEP_F SEP_B HAP HVA VAHI BS0 KH RSK RPF RBI RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ apply F_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP]
          | intros; eapply F_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
Proof using SFR SFL TOK HOUT HSTRN HF LO GLO QHI TQ HA SEP_F SEP_B HAP HVA A0 VAHI BS0 KH RSK RFM RPF RBI RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B.
    first [ intro; apply F_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
          | intros; eapply F_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_P1 : S_P1.
Proof using HF LO HA A0 RG_stk RG_img RG_fmt.
    first [ apply F_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
          | intros; eapply F_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_PRO : S_PRO.
Proof using LO GLO QHI HA HAP HVA RG_stk RG_img.
    first [ apply F_printf_core_pro.L_PRO; first [eassumption]
          | intros; eapply F_printf_core_pro.L_PRO; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RB | exact RNG | exact rstk | exact rfmt | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.

  Let HS_PRO := L_PRO.
  Let HS_HEAD := L_HEAD.
  Let HS_P1 := L_P1.
  
  (* [comment removed for export] *)
  Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
      let _ := ctx_all in
      SINK m0 st -> stk bsegs m0 lo q -> mem_inv bsegs m0 -> bytes_at bsegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      rw_cells bsegs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
      args_ok Fp B BS RNG m0 lo q AP (skipn (Z.to_nat i) slots) args ->
      Forall (fpcall_stmt Fp B BS RB SINK TOPOK OUTFP) (fp_calls (length fmt) fmt args) ->
      (0 < Fp)%Z -> (Fp + 232 <= 2^64)%Z ->
      implAM RNG (printf_model OUT OUTFP fmt args) st POST
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0xa7e48) fc0 None m0 (seg_rom bsegs)).
Proof using SFR SFL TOK HOUT HSTRN HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 KH RSK RFM RPF RBI RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt RR_stk RR_fmt RR_B ENV0 RC_stk RC_fmt RC_B HS_PRO HS_HEAD.
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 st i args _ HS0 ST0 MI0 BY0 VAA0 SSP0 APC0 Hi AOK FPC HF0 HF1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    unfold printf_model. ienter.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Fp); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    pose proof FI as FI'. destruct FI' as (MI & MU & WM & _).
    assert (HS : SINK m st).
    { eapply (SFR [(q + -544, q)]%Z m0 m st HS0 MUq WM); (apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]). }
    assert (APC : rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
    { eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
    stmt (HS_HEAD (length fmt)) as NXH.
    jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
      [ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
      | exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
      let _ := ctx_all in
      stk bsegs m0 lo q -> mem_inv bsegs m0 -> bytes_at bsegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      pass1_ok fmt = true ->
      evtF bsegs RNG (POST1 0)
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0xa7e48) fc0 None m0 (seg_rom bsegs)).
Proof using Fp B BS HF LO GLO QHI HA HAP HVA A0 RG_stk RG_img RG_fmt HS_PRO HS_P1.
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 _ ST0 MI0 BY0 VAA0 SSP0 P1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 0%Z); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    stmt HS_P1 as NX1.
    jump (eapply NX1; [ exact FI | eapply munch_weaken; [|exact MUq]; unfold sub_fp; cbn [outside]; intros; lia | exact LOW | exact DIG | exact PAD | exact P1 ]).
  Qed.

End PrintfCore.


(* [comment removed for export] *)
Theorem printf_core_proof : forall (St : Type) (Fp B BS : Z) (RB : region) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
    (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z),
  sink_frame_stmt Fp B BS SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK -> out_stmt Fp B BS RB SINK TOPOK OUT ->
  strnlen_a_stmt ->
  printf_core_stmt Fp B BS RB SINK TOPOK OUT OUTFP.
Proof using Type.
  intros St Fp B BS RB SINK TOPOK OUT OUTFP SFR SFL TOK HOUT HSTRN.
  intros RNG rstk rfmt ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary fmt VA i slots args
         HS BY HF Ha0 APC VAA Hi AOK FPC ST LO GLO SPHI TQ SSP MI FRM HA BS0 SEPF SEPB HAP HVA VAHI
         KH ENV RCS RSlo RShi RCF RFM RPF RCB RBI RGstk RGimg RGap RGva RGF RGB RGfmt RRS RRF RRB.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  pose proof (@L_CORE2 St Fp B BS RB SINK TOPOK OUT OUTFP SFR SFL TOK HOUT HSTRN RNG rstk rfmt ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) VA slots a3 a4 HF LO GLO SPHI TQ FRM HA SEPF SEPB HAP HVA (proj1 Ra1) VAHI BS0
                      KH (conj RSlo RShi) RFM RPF RBI RGstk RGimg RGap RGva RGF RGB RGfmt RRS RRF RRB ENV RCS RCF RCB
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 st i args HS ST MI BY VAA SSP APC Hi AOK FPC) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply implAM_mono.
  { apply C; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; lia. }
  cbv beta. intros r st' ms' P. unfold POST, W in P. unfold printf_core_post, SR.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & apv & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & HS' & SSP' & APC' & Hr).
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', apv, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact Hr.
Qed.

Theorem printf_core1_proof : printf_core1_stmt.
Proof using Type.
  intros RNG rstk rfmt ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
         BY HF P1 Ha0 ST LO GLO SPHI SSP MI HA HAP A2HI KH ENV RCS RSlo RShi RCF RFM RPF RGstk RGimg RGfmt RGap RRS RRF.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in LO, GLO, HA.
  pose proof (@L_CORE1 737200 68436 0 rfmt RNG rstk rfmt ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) (bv_unsigned a2 + 8)%Z [] a3 a4 HF
                      ltac:(unfold PC_DEPTH; lia) ltac:(unfold GLOBALS_TOP; lia) SPHI HA HAP ltac:(lia) (proj1 Ra1)
                      RGstk RGimg RGfmt
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ST MI BY) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply evtF_mono.
  { apply C; [ | exact SSP | exact P1 ]. unfold va_area. cbn [u64s map concat]. apply bytes_at_nil; lia. }
  cbv beta. intros ms' P. unfold POST1 in P. unfold printf_core1_post.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & SSP').
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact SSP'.
Qed.
End CANSEC1.
