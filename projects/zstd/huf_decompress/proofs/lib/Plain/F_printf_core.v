(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (34 recorded proofs replaced by written proofs (L_EXIT, L_END, L_EXIT1 and 31 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_memset F_memcpy F_memchr F_strnlen Stdio_kit F_syscalls StdioFiles.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import Printf_zfacts F_printf_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require F_printf_core_exit F_printf_core_end F_printf_core_exit1 F_printf_core_scan F_printf_core_flags F_printf_core_width F_printf_core_prec F_printf_core_state F_printf_core_dir F_printf_core_t6 F_printf_core_t5 F_printf_core_t4 F_printf_core_t3 F_printf_core_t2 F_printf_core_t1 F_printf_core_tail F_printf_core_intc2 F_printf_core_intc F_printf_core_dloop F_printf_core_fmtu2 F_printf_core_fmtu F_printf_core_cvd F_printf_core_cvu F_printf_core_xloop F_printf_core_cvx F_printf_core_cvs F_printf_core_cvfp F_printf_core_conv F_printf_core_head F_printf_core_p1 F_printf_core_pro.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Export F_printf_core_common.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_printf_core () := "C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainBF_printf_core_exit6L_EXITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface?sink_frame_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4mpadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common4POSTC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib5PlainAF_printf_core_end5L_ENDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core6L_EXITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainCF_printf_core_exit17L_EXIT1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainBF_printf_core_scan6L_SCANC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainCF_printf_core_flags7L_FLAGSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainCF_printf_core_width7L_WLOOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common7S_WLOOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainCF_printf_core_width7L_WIDTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainBF_printf_core_prec7L_PLOOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common7S_PLOOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainBF_printf_core_prec6L_PRECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainCF_printf_core_state7L_STATEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core7L_WIDTHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core6L_PRECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainAF_printf_core_dir5L_DIRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core7L_FLAGSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core7L_WLOOPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core7L_PLOOPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core7L_STATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain@F_printf_core_t64L_T6C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain@F_printf_core_t54L_T5C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core4L_T6C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain@F_printf_core_t44L_T4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core4L_T5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain@F_printf_core_t34L_T3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core4L_T4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain@F_printf_core_t24L_T2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core4L_T3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain@F_printf_core_t14L_T1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core4L_T2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainBF_printf_core_tail6L_TAILC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core4L_T1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainCF_printf_core_intc27L_INTC2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core6L_TAILC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainBF_printf_core_intc6L_INTCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core7L_INTC2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainCF_printf_core_dloop7L_DLOOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainCF_printf_core_fmtu27L_FMTU2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core6L_INTCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainBF_printf_core_fmtu6L_FMTUC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core7L_FMTU2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core7L_DLOOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainAF_printf_core_cvd6L_CV_DC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core6L_FMTUC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainAF_printf_core_cvu6L_CV_UC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainCF_printf_core_xloop7L_XLOOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainAF_printf_core_cvx6L_CV_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core7L_XLOOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainAF_printf_core_cvs6L_CV_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainBF_printf_core_cvfp7L_CV_FPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainBF_printf_core_conv6L_CONVC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core6L_CV_DC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core6L_CV_UC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core6L_CV_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core6L_CV_SC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core7L_CV_FPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainBF_printf_core_head6L_HEADC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib5Plain=F_printf_core6L_SCANC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core5L_DIRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core6L_CONVC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core5L_ENDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain@F_printf_core_p14L_P1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core7L_EXIT1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainAF_printf_core_pro5L_PROC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib5PlainDF_printf_core_common7ctx_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9F_pop_arg7va_areaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib5Plain>F_printf_iface7args_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib5Plain>F_printf_iface;fpcall_stmtC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib6Common<Printf_model8fp_callsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common5S_PROC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5PlainDF_printf_core_common4finvC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common8lo_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common8hi_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common6S_HEADC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;printf_loopC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics5Riscv7Prelude4tree00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib5PlainDF_printf_core_common8Fok_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common;implM_eq_msC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model<printf_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib5Plain:F_syscalls7got_sspC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8pass1_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common5POST1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common4S_P1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec6evt_eqC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic5False00c59OSSVerify5KrLib5Plain=F_printf_core7L_CORE2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface?sink_flags_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface:topok_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface8out_stmtC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface@printf_core_postC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05I47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics5Riscv3Sem7reg_getC59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common3FokC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface@printf_core_stmtC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5Plain>F_printf_iface8PC_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles;GLOBALS_TOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface<STATIC_SPLITC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib5Plain>F_printf_ifaceAprintf_core1_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=F_printf_core7L_CORE1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common<bytes_at_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_ifaceAprintf_core1_stmtC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)
(* [comment removed for export] *)

Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
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
  Hypothesis HA : (A + zlength fmt <= 155648)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((156856 <= Fp /\ Fp + 232 <= 359072) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((359080 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  (* [comment removed for export] *)
  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
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
  Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
  Ltac rd_fmt idx :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 156792 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 228064 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := cbv delta [psegs psegs] in *; fold psegs in *.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp);
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
      repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
    end.

  (* [comment removed for export] *)
  Lemma L_EXIT : S_EXIT.
  Proof using LO.
    first [ apply F_printf_core_exit.L_EXIT; first [eassumption]
          | intros; eapply F_printf_core_exit.L_EXIT; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_END : S_END.
  Proof using GLO HAP LO SEP_F VAHI.
    first [ apply F_printf_core_end.L_END; first [eassumption | eexact L_EXIT]
          | intros; eapply F_printf_core_end.L_END; first [eassumption | eexact L_EXIT] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_EXIT1 : S_EXIT1.
  Proof using LO.
    first [ apply F_printf_core_exit1.L_EXIT1; first [eassumption]
          | intros; eapply F_printf_core_exit1.L_EXIT1; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_SCAN : S_SCAN.
  Proof using A0 HA HF.
    first [ apply F_printf_core_scan.L_SCAN; first [eassumption]
          | intros; eapply F_printf_core_scan.L_SCAN; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FLAGS : S_FLAGS.
  Proof using HF.
    first [ apply F_printf_core_flags.L_FLAGS; first [eassumption]
          | intros; eapply F_printf_core_flags.L_FLAGS; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_WLOOP : S_WLOOP.
  Proof using HF.
    first [ apply F_printf_core_width.L_WLOOP; first [eassumption]
          | intros; eapply F_printf_core_width.L_WLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
  Proof using HF.
    first [ intro; apply F_printf_core_width.L_WIDTH; first [eassumption]
          | intros; eapply F_printf_core_width.L_WIDTH; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PLOOP : S_PLOOP.
  Proof using HF.
    first [ apply F_printf_core_prec.L_PLOOP; first [eassumption]
          | intros; eapply F_printf_core_prec.L_PLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PREC : S_PLOOP -> S_PREC.
  Proof using HF.
    first [ intro; apply F_printf_core_prec.L_PREC; first [eassumption]
          | intros; eapply F_printf_core_prec.L_PREC; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_STATE : S_STATE.
  Proof using HF.
    first [ apply F_printf_core_state.L_STATE; first [eassumption]
          | intros; eapply F_printf_core_state.L_STATE; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DIR : S_DIR.
  Proof using HF.
    first [ apply F_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE]
          | intros; eapply F_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T6 : S_T6.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ.
    first [ apply F_printf_core_t6.L_T6; first [eassumption]
          | intros; eapply F_printf_core_t6.L_T6; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T5 : S_T5.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_t5.L_T5; first [eassumption | eexact L_T6]
          | intros; eapply F_printf_core_t5.L_T5; first [eassumption | eexact L_T6] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T4 : S_T4.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_t4.L_T4; first [eassumption | eexact L_T5]
          | intros; eapply F_printf_core_t4.L_T4; first [eassumption | eexact L_T5] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T3 : S_T3.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_t3.L_T3; first [eassumption | eexact L_T4]
          | intros; eapply F_printf_core_t3.L_T3; first [eassumption | eexact L_T4] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T2 : S_T2.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_t2.L_T2; first [eassumption | eexact L_T3]
          | intros; eapply F_printf_core_t2.L_T2; first [eassumption | eexact L_T3] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T1 : S_T1.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_t1.L_T1; first [eassumption | eexact L_T2]
          | intros; eapply F_printf_core_t1.L_T1; first [eassumption | eexact L_T2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_TAIL : S_TAIL.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
          | intros; eapply F_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_INTC2 : S_INTC2.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL]
          | intros; eapply F_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_INTC : S_INTC.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2]
          | intros; eapply F_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DLOOP : S_DLOOP.
  Proof using GLO LO QHI.
    first [ apply F_printf_core_dloop.L_DLOOP; first [eassumption]
          | intros; eapply F_printf_core_dloop.L_DLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FMTU2 : S_FMTU2.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC]
          | intros; eapply F_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FMTU : S_FMTU.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
          | intros; eapply F_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_D : S_CV_D.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU]
          | intros; eapply F_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_U : S_CV_U.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU]
          | intros; eapply F_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_XLOOP : S_XLOOP.
  Proof using GLO LO QHI.
    first [ apply F_printf_core_xloop.L_XLOOP; first [eassumption]
          | intros; eapply F_printf_core_xloop.L_XLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_X : S_CV_X.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
          | intros; eapply F_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_S : S_CV_S.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL]
          | intros; eapply F_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_FP : S_CV_FP.
  Proof using GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ.
    first [ apply F_printf_core_cvfp.L_CV_FP; first [eassumption]
          | intros; eapply F_printf_core_cvfp.L_CV_FP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CONV : S_CONV.
  Proof using BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP]
          | intros; eapply F_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using A0 BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ intro; apply F_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
          | intros; eapply F_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_P1 : S_P1.
  Proof using A0 HA HF LO.
    first [ apply F_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
          | intros; eapply F_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PRO : S_PRO.
  Proof using BS0 GLO HA HAP HVA LO QHI SEP_F.
    first [ apply F_printf_core_pro.L_PRO; first [eassumption]
          | intros; eapply F_printf_core_pro.L_PRO; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.

  Let HS_PRO := L_PRO.
  Let HS_HEAD := L_HEAD.
  Let HS_P1 := L_P1.
  
  (* [comment removed for export] *)
  Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
      let _ := ctx_all in
      SINK m0 st -> stk psegs m0 lo q -> mem_inv psegs m0 -> bytes_at psegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      rw_cells psegs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat i) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls (length fmt) fmt args) ->
      (0 < Fp)%Z -> (Fp + 232 <= 2^64)%Z ->
      implM psegs (printf_model OUT OUTFP fmt args) st POST
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x20220) fc0 None m0 (seg_rom psegs)).
Proof using FRM0 HS_HEAD HS_PRO.
ltac2:(KReplay.run1 (kr_t_F_printf_core ()) ["PrintfCore"] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with58__sat129h68__sat130h78__sat131h88__sat132h94__p1h:4__x2h;3ms'h<2Hah=4__p2h>4__x3h?4__x4h@1HhA2_HhB4__x5hC2ivhD3AOKhE3APChF4APC0hG3BY0hH3DIGhI2FIhJ3FI'hK3FPChL3HF0hM3HF1hN2HShO3HS0hP2HihQ3LOWhR2MIhS3MI0hT2MUhU3MUqhV3NXHhW3NXPhX3PADhY4SSP0hZ3ST0h[4VAA0h\2WMh]7__sat32h^7__sat33h_7__sat34h`7__sat35ha3a0'hb3a1'hc3a2'hd3a3'he3ahihf3alohg4argshh4cstrhi5cstr0hj4digshk1ihl4j128hm1mhn1pho3padhp3pfxhq2plhr3plphs3s2sht2sthu3x15hv3x16hw3x17hx3x28hy3x29hz3x30h{3x31h|2x5h}2x6h~2x7i002zap%0p%1p&0p;1p;Lp;2p;3p;9p;7p;Op;4p;Jp;<p;6p;>p;5p;:p;Up;8g019Nj12Tg01:3j1iTg01:Qj1oTg01;4j1sTg01;TmL0gTg01<[j2tTg01=Ok10XTg01>Jj3KTg01?Fk20ITg01@Ej1PTg01@ck20@Tg01A@j2:Tg01A]j2;k10vTg01BCj1nTg01C8j1vTg01CXk10_Tg01D8k30]Tg01DVm90ZTg01EWj2bTg01F7k70WTg01G<j2~Tg01G\k30TTg01H]k30PTg01I>j2ZTg01IZj18Tg01J?j2{Tg01J\j21Tg01K8k10HTg01Knk10FTg01Lfj3rTg01MCj3wTg004imL0AmJ0BTg01M`k20|Tg01NTlOVTg01OFk109Tg01Ohk10sTg01PaS00j7[k60?k50>k40=k30<k203k10;Tg01QSmO0iTg01RXk205Tg01S@k30:Tg01Sdj2cTg01TBk10bTg01T`k10aTg01UKj2RTg01Unk30`Tg01VQk204Tg01W4j4mTg01W_k20^Tg01XAj24Tg01X[k20\Tg01YGj3kTg01Yak30[Tg01Z@k40YTg01[2S01j26Tg01[Mk102Tg01[omJ01Tg01]3j1jTg01]Qk40VTg01^1j3UTg01^Qj3aTg01_Em<0UTg01`Mj10Tg01`lj2|Tg01aak60NTg01bbm>0MTg01cjj3pTg01d[j2DTg01e5j2STg01e^j2fTg01fJk10JTg01fhk30GTg01gKj2yTg01ghj2zTg01hIk600Tg01hjk50KTg01iNk10ETg01jGj1qTg01jgk30LTg01kcm:0DTg01ldmU0CTg01mjj7}k80hTg01nnk10QTg01o[j27k10xTg020=j4=j3Ej2dk10yTg005mk20{Tg020jk10zTg021Wk106Tg006Yj83Tg022<k10rTg023Dm90qTg024Ok40pTg003kk80mTg025Ek707Tg026:k50lTg027?k40jTg0281k40kTg028fj4xTg029\k70nTg02:Ok30oTg02;2k708Tg02;Vk70fTg02<:k80eTg02<^k30dTg02=Rk30tTg02>;k40uTg02>Yk60cTg02?=k70wTf0R0#2#2p=<g02?aR1f2R2f1R3P0H0jp=NP1P2P3P0H0kp=Mg02@VR4?U30p=YP1P2P3P0Cxp=?g02AKR5/10p=@%20#2#2#Pp=Jf6R6f5R7f4R8f3R9P2P3P5P0L0hp=T%20#2#2#2p=W%20#8p=9g02AiR:P1P8P9P2P3P0K0np=e%80#8p=lg02B^R;0040p=FB0o;30p=HP2g02C<S02g02C[R<P<g02D;S03P;P3g02D[P0Cmg02EBR=K08p=5P3Q02P<P<Q03P0P=K08p=uP2Q02P<P<Q03P3P0K0fp=XP9Q02P<P<Q03P2P3P0L0ep=>1:23/10p=G%80#2p=B%00#0p>0S%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p>0R%00#0#0#0#0#0#0#0p>0O%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=OB0d130p=]P1P3g02EbP0Cxp=^P1P3g02F_R=P0Cxp=\1630,62p=h1630,62,69,68p=_%80#8#8#8p=CB0t;30p=LP;P2P3P0H0up=QP3Q02P<P<Q03P0J0cp=gP2Q02P<P<Q03P3P0K0wp=`f7S04P6P71789P2C=P3P0C=p=IP8P91723P0C=p=Ag02G^R>#2S05#2S06#2R?#<S07#2R@#iRA#oRBp,2StRCg02HC#sp,2raRDp,1qREp,2gpRFp,2tpRGp,3s0eRHp,3s1eRIp,3s2eRJp,3s3eRKp,3s4eRLp,3s5eRMp,3s6eRNp,3s7eROp,3s8eRPp,3s9eRQp,4s10eRRp,4s11eRSp,1FRTp,3fc0RUp,2m0RVp,2loRWp,6canaryRXp,1ARYp,3fmtRZp,2APR[p,2VAR\p,5slotsR]p,3nlaS08p,3nltR^NL0gP<p,4SINKS09PVP9O2ANVWE1t1V&0XZR_9MVYAKV\]20IVX%P?R`f8Ra+0@,:\,;A#n%v4R4'Y9?V[f9Rb#@p,2FpRcp,1BRdp,2BSRePVPWPEP[f:Rf$0_>0]B]PbN90Z1b;;Rg/b;/b;/b;PCPcPdPeQ09p,5TOPOKS0:p,5OUTFPRhK0W1~;ZRi@0TZf40P1Z5c%8>S0;#8S0<#2Rj#8#JRk,:cS0=Q05#PRl%P@R@'{Rm'1P:P1&0H1S0>1b;CR:$0FS0?PCp,3OUTRnPhPiPZf=S0@f?S0AFTPCPcPdPeQ09PDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPVPWPXP[Ar;C0Aw;C0NL0AXn:-0|:S0BPD1;AEPFPGfIS0CfHR:fGRoPHPI1;AcS0D1;AYS0E1;A[Q08P^fFS0FfES0GfDRpPJPKPLPMPNPOPPPQPRPSfCRqfBS0HfAS0If@S0JMOVPT%<>#W#9#<#9#<#J,;APU&09BRrPV&0s1RsF[S0Kp,6HS_PROPcPdPePDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]Q08P^NO0iP0fJS0LQ0CP:PoQ0FQ0GPpPqQ0HQ0IPcg02IBRtQ0>Q0?PCPnPhPiPZQ0AQ0IFTQ0BP0DeW;f;S0MPfPbPaQ04Q05#8S0N#lRu#8#PRv-05lS0O1Z5lRw%@v1{lvRx,Z5[[S0P%@lRyg02JIRzB0:lv3UW<S0Q%@x\z^<yS0R205l@S0S%@@1Z5m[\wS0TB0:l@3VzX<yS0U%@m\z^<yS0Vg02JeRy#vR@%syS0W1c;3S0X&0b;S0Y&0a;Rw1R;>Rx%FkS0Z'H%Fl>0`;ARl55w&09<RvPwP;204;5R{g02KQR|PxCm,uwPvA5w{xS0[P;PxP|PlCm,uw5XwC>C>Q03-0^wS0\P0P2g02L8Rlg02LXR|'420\02=kl|dB0[;53H0YS0]b2b3b4X0;AG0km1Z53%@21Z2m'6[[^0;P0PcP6Q04O3b1b]b^b_b`%i?#oRm$02\BR|%smS0^Q0^Q0^PcPdPePDPEPHPIPJPKPLPMPNPOPPPQPRPSPVPWPXPYPZP[P\P]f>S0_NJ01P;P;%B?#W#jS0`,:ERmPEH0VS0a%vgS0b5UgS0cQ0A7aVQ0JP[Q08P^Q0AQ0_Q0@f<S0dQ0M1;A5RlPfPbPaN<0U7?mQ0IQ0;#2S0e#<#B#<#j,:Eg02M8S0f#0S0g#0S0h#0S0i#0S0j#0S0k#0$0S$0RR}/|a/Y43?Q0H%Wu#j,:E&0O}#O#O#O#O#O#O#O/|a/Y43?P8PcPdPePDPEPHPIPJPKPLPMPNPOPPPQPRPSPVPWPXPYPZP[P\P]PqNJ01Q011t1pPcPdPePEPWP[J0NRq?aVp1]Vp%2j#<#j,:ERjPDPHPIPJPKPLPMPNPOPPPQPRPSPXN>0MR}5?pANpWmAMpY_AKp\]1;A=#n/Y4R=,^p%nX/Y4Ru,\p'63hD_Q0>Q0?PCPnPhPiPZfUfWS0lFTQ0BP0DeX;tPD1;AmS0mPFPGf`S0nf_R~f^S0oQ06#8#9#P,;AS0pQ0<#C#C#C#C#C#C#C#PS0<,;AS0qPfPbPaQ04P^f]S0rf\S0sf[RbPJPlQ0DQ0EPNPOPPPQPlPSfZfYS0tfXS0uQ0lMOVPT%<>#W#9#9#B#B#J,;ARfPUPrQ0GPsF[5p1P0Q0F,t1AaqVo1]VoA?oj}ANoWmAMoY_AKo\]1^o=1\ou'63hD_Q01AaqV:1]V:A?:j}AN:WmAM:Y_AK:\]1^:=1\:u3hD_Q0>Q0?PCPnPhPiPZQ0tPbFTQ0BP0DeX;tPDQ0mPFPGfdS0tfcS0vfbS0wQ0pQ0qQ0_Q0@Q0dQ0MP^faS0MQ0nP~PJPlQ0DQ0EPNPOPPPQPlPSQ0oQ0rQ0sPbMOVPTPfPUPrQ0CPsF[5p1P0Q0L9aqVfKRq,]VA?qj}ANqWmAMqY_AKq\]1^q=1\qu3hD_Q01fLRb,]VA?bj}ANbWmAMbY_AKb\]1^b=1\bu'6D_Q0>Q0?PCPnPhPiPZQ0rP~FTQ0BP0DeX;tPDQ0mPFPGfhS01fgS0sffS0dQ0pQ0qQ0HQ0IQ0JQ0AP^feS0_Q0tQ0vPJPlQ0DQ0EPNPOPPPQPlPSQ0wQ0MQ0nP~MOVPTPfPUPrfMS0nPsF[5p1P0fNS0x,]VfOR~??j}AN~WmAM~Y_AK~\]1^~=1\~u'6D_p,3SFRQ0cPVfPS0yQ0MQ0rQ0JP3PgAw;;0S0r/1cQ0=Ar;;0S0z'1'DXCgS0{Q0aQ0bQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0Vp-0RuQ0j,S;S0jQ0i,S;S0iQ0h,S;Q0f,S;'L'LS0f'Lg02MWR='fQ0k,S;Q0jQ0g,S;S0g'L'L/f==Uy@5UyQ0W&0J;R_1c;87Q21c;9S0k7Q3Q0YPwQ0e,R;R}95wxPvPw1gw6Q05,R;RjQ0Z'HS0Z%2>#B#C#9#9#9#<#JS05#F55w5Xw%F`S0e,H}=5wjQ04,gwS0h5Xw5`wPvPw%2>#l#<#B#W#W#JS0|#FQ0;,R;R}55wPvPwQ0N#2#<#B#<#JS0;#F:0G;xS0}95w}PvA5wxjS0~Q0ZQ0`#F,HxS1055w5`wC>C>C>C>Q0\Q0]b2b3b4X0;X:;X>;X?;X9uW=1109Q059G2k,67AG8`2/66'DQ0|/18Q0;,y9,171187Q0`,:89G7k'D[[[[^0;^:;^>;^?;^9u^=uP0Q0=/1\%<>#l#<#B#9#9#l#J/1cP[PWPcPEp,3HAPS0|p,5SEP_Fp,3GLOp,2LOS05O:b1b5b6b7b8Q0a9w;;S0Z/1cQ0=Q0a9r;;S11'1'DeQ0{,zgJ00PgQ0r/1d1:deRkQ0z'1'DXCgS0zQ0aQ0bQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0f/f=Q0jQ0iQ0g'L'L/f==Uy@5UyQ0W1c;7?Q8_?Q2_Q0k7Q3Q0YPw1R;?R?95wxPvPwQ0h1Hj}R}Q06,R;Ry55w5XwQ0e,H?=5wj1gwa5Xw5`wPvPwQ0}95wyPvQ0~Q1095w}5`wC>C>C>Q0\Q0]b2b3b4X0;X:;X>;X?;XB;X9uX=u1108AG298,66AG7`2Q04'6'DQ0;,y2,171198Q0`,:99G87'D[[[^0;^:;^>;^?;^B;^9u^=uP011k\%2>#B#C#9#9#9#9#J/1dP[PWPePdPEQ0|p,5SEP_BQ05O:b1b5b6b7b8Q0Z/1dQ11,1k'DeQ0z,zgJ00O9Q09Q0yQ0MO2P1Q0cPVfQRgP[Q0M-0@`,:\,;A#n/Y4R4Q0uQ0IP2Q0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VP@Q0W1c;2?Q3_Q0YPwA5wjxRjPv1gw8=`wjPwQ02P<P<Q03I0K5XwC>Q0\Q0]b2b3b4X0;X:;X9u11301123,D9/6z[^0;^:;^9uP0AG[`mPEP[Q0|O4b1b5b6b7b8Q0c&0E4#q80L[eN:0DA?g[4p,7HS_HEADPiO1PCPcPdPeQ09Q0:PnPhPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]Q08P^PiNU0CP1Q0>Q0?PCPnPhPiPZQ0vQ0_FTQ0BP0DeX;tPDQ0mPFPGfnR\fmR4flRmQ0pQ0qP:PoQ0FQ0GP^fkR`fjRufiRzPJPlQ0DQ0EPNPOPPPQPlPSQ01Q0sQ0dQ0_MOVPTPfPUPrfSR9PsF[R<PCP;PCPnPhPiPZQ0wP5F}Q0tPCPcPdPeQ09PDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPVPWPXP[NJ0BR[P<PDQ0mPFPGP\P4PmQ0pQ0qP:PoQ0FQ0GP^P`PuPzPJPlQ0D1:Y5RX,;ARWPNPOPPPQPlPSQ01Q0sQ0dQ0_MOVPTPfPUPrP9PsF[RVP|PtPBPBPBPBPBPB&0QBRRPBQ0_PR17B`PRGIPBPmPBPRPBPOPRDA17BFPBPBPRPBPlPRDARlPBPoPBPRPBPSPRDADAGIRF17BDRMPBPBPBPRPBPzPRQ0q,7BPBPRPBPQPRDAGIRL17B\RKPBPBPRQ0E,7BRIPRC=RHQ0G,7BREPBPRPBQ0sPRDAReC=RdC=RcC=RjPrPBPBPBPBPRPBPuPRQ0p,7BPBPRPBPPPRDAGIPBPGPBPBPRPBQ0DPRQ0F,7BPBPRPBQ01PRDAGIQ0m,7BPBPBPBPRPBPJPRDAPBP:Pl17B4PBPBPRPBPNPR17B^PBPRPBQ0dPRDAGIGIGIRlC=RGPTPfPUPrP9J0?PBPBPFPMPBPLPKPBPBPR17BWR8PRC=RkPEPeC=R>C=R7C=R6PrPlC=R}PTPfPUPrP9J0?PsPsP|Pt\|RyPGPTPfPUPrI0>P}PTPfPUPrI0>P9P9&02BRaPy\|RyPGPTPfPUH0=P}PTPfPUH0=PrPrQ07#i#oR?Py\aRyB0<GTfB0<}TfPUPUPBPy\?Ry203GT203}TPfPfQ0N#i00{BR=Py\BRy&0;G&0;}PTPTP=Py\=RyQ00Q00PGP}Py\=Q00'4&0zBRyP=AEBjrAEB6rPlPlPaP=\yR}1dBj1dB6PrPrPyP}\aR}&0yBRGPGPjP6P}\y/4GPyPyAEBFMRMPMPcP7Py\yR7/4MPyPyAEBLKRKPKPdP>147KPyPyAEBHEAEBkEPePePaP71dBH1dBkPEPEPyP7\aRKPGPGPHPkPK\y/4GPyPyAEBRIAEBR8PRPRPaP71dBRR7P7PIP814K7PBPa&0xBR7P7Q0EPWPa\B/47P;PB&0vARAPAPYPXPB\;/4A&06i%qi#@1~B]R]$06%q]#@Q0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VP@Q0WQ0XQ0YP;Pxg02NC1Hx{Cm,uwQ0\Q0]b2b3b4X0;1:059k;0^0;P0PYO1b1b5b6b7b8bibhAk;YXRXePXeG3G3G314yRG3G314aEG314yeG3G3G3G314arRaG314ylG3G314=TG314BfG314?UG3PaG314|9G314|sG3Akt<VeP0PDP\P4PmP:PoQ0FQ0GP^P`PuPzPJPNPOPPPQPSQ01Q0sQ0dQ0_PTPUP9Q0tP5P5P5Q0vQ0wfRPgQ0yP~Q0xQ0nPbPqQ0LQ0CPpQ0HQ0IQ0JP2P3Q0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VP@Q0WQ0XQ0YPwQ0[PvQ0[C>Q0\Q0]b2b3b4X0;%@0%@3[^0;P0Q01Q0oO2b1b5b6b7b8Q0uQ0lp,4FRM0&0rTQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VP@Q0WP_Q0YA5w{{Q0\Q0]b2b3b41155P0b1b5b6b7b8RTPTPTQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VP@Q0WP_Q0Y1H{{Q0<#F55wQ0\Q0]b2b3b41:55RwQ0<'1P0b1b5b6b7b8g02Nj,1weOhN90qH0pbVbEbNWAW\P3P0O2n2001000010121000000W@WTP3P0O2n2001000010121000000W@WRP3P0O2n2001000010121000000bJWXWHWQWUWIXdBXcBXbBXaBWoWjWlXeBXfBXrBXqBZ00BXsBXpBWmOCbWL0mPCP1P;PCPnPhPiPZQ0@P5F}Q0AP[Q0KK07ePCP1P;PCPnPhPZQ0@I0lQ0AP[Q0KK07eWMWLWKWDWPWFWYW[WGWSWZWObAWgXk;WtX{BXzBXyBXxBXwBXvBXuBX~BX}BW|o"). Qed.

  (* [comment removed for export] *)
  Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
      let _ := ctx_all in
      stk psegs m0 lo q -> mem_inv psegs m0 -> bytes_at psegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      pass1_ok fmt = true ->
      evt psegs (POST1 0)
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x20220) fc0 None m0 (seg_rom psegs)).
Proof using HS_P1 HS_PRO.
ltac2:(KReplay.run1 (kr_t_F_printf_core ()) ["PrintfCore"] "h02Hah17__arithh24__ffh34__p1h48__varmaph55__with64__x1h74__x2h84__x3h91xh:3BY0h;3DIGh<2FIh=3LOWh>3MI0h?3MUqh@3NX1hA3NXPhB2P1hC3PADhD4SSP0hE3ST0hF4VAA0hG2_HhH8__sat129hI8__sat130hJ8__sat131hK8__sat132hL7__sat32hM7__sat33hN7__sat34hO7__sat35hP3a0'hQ3a1'hR3a2'hS3a3'hT3ahihU3alohV4digshW4j128hX1mhY3padhZ3pfxh[2plh\3plph]3s2sh^3x15h_3x16h`3x17ha3x28hb3x29hc3x30hd3x31he2x5hf2x6hg2x7hh2zap%0p&0p;1p;Lp;4p;2p;3p;Op;Fp;Jp;<p;7p;6p;5p;8g019Nj13Tg01:3j1RTg01:Qj1MTg01;TmL0:Tg027?j4|Tg01<[j2rTg01=Oj1nTg0281j4jTg01>Jj3fTg01?Fj2cTg02Ocj1aTg01YGj3DTg01QSmO09Tg02PdmF04Tg01@Ej19Tg01IZj11Tg01RXj2VTg01I>j2=Tg01J\j25Tg01J?j2STg01S@j3QTg01C8j1GTg01;4j1YTg01fJj1iTg01TBj1hTg01T`j1gTg01VQj2BTg01Unj3bTg01W4j4FTg01W_j2`Tg01XAj2LTg01X[j2_Tg01Yaj3^Tg01Z@j4]Tg01[2j2:Tg01[Mk108Tg01[omJ07Tg01EWk206Tg01]3j1JTg01A@j2ATg01]Qj4\Tg01^1j3?Tg01^Qk302Tg01A]j2>Tg01_El<{Tg028fj4ITg01`Mj10Tg01`lj2NTg02QilOtTg01NTlOqTg01OFj1UTg01Ohj1pTg01Paj7TTg01nnj1oTg01o[j26Tg02Rmj1mTg01e5j2HTg02=Rj3XTg01e^j2lTg01Sdj2OTg02>;j4sTg01UKj2ETg02>Yj6kTg01fhj3xTg02:Oj3yTg01hjj5zTg01gKj2}Tg02SFj2ZTg02T<j2~Tg02U1k600Tg02Ulk601Tg02;2j7eTg02;Vk703Tg020=j4KTg02V`j6dTg02<:k805Tf0R0#3#3p=2%10#1p=Wg02B^R1f1R2g02D[P0CFp=CP2g02C<R3g02C[R4P4g02D;R5P0g02EBFep=<f2R6P3P4P4P5P2P0K03p=@%00#0#0#0p=w%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=v%00#0#0#0#0#0#0#0p=u%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=8%10#1#1#1p=;f7R7f6R8f5R9f4R:f3R;'6P6CKP2P0CKp=7P:P;1662P0CKp=4P2P3P4P4P5P0Edp=PP;P3P4P4P5P6P2P0L05p=[g02G^R<#3R=#3R>#3R?#3#2R@#RRA#MRBp,2raRCp,1qRDp,2gpREp,2tpRFp,3s0eRGp,3s1eRHp,3s2eRIp,3s3eRJp,3s4eRKp,3s5eRLp,3s6eRMp,3s7eRNp,3s8eROp,3s9eRPp,4s10eRQp,4s11eRRp,1FRSp,3fc0RTp,2m0RUp,2loRVp,6canaryRWp,1ARXp,3fmtRYp,2APRZp,2VAR[p,5slotsR\p,3nlaR]p,3nltR^NL0:P4g02?aR_PUPVPDC|1r_UP_PUPX%nYCjAfU[\1cUWg02L8R`%aYg02LXRa3Dp,6HS_PROp,2FpRbp,1BRcp,2BSRdPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^NO09P0fARef@Rff?Rgf>Rhf=Rif<Rjf;Rkf:Rlf9Rmf8Rng02AKRoPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPoNF04S00P8P9P:P;P6%9=Rp%1=Rq#WRr#1#9Rs'VS011=opRt15os1SpsRu,=o[[S0215opRvg02JIRwAQps2UW0S0315ou\w^0vS04%9@R@,VpS0515o@1Sp@Ru,=oRs[\tS06AQp@2VwX0vS0715ou\w^0vS08g02JeRv#GRu%YvS09%i1%h1S0:%g1R@1B1oRt/Ct,<@P1Ptg02KQS0;1B1p=b1ACF,<@3@1`@5S0<P0P61L`a1_06=D`adA^1o2C]S0=b2b4b515oo/:sP0b1bLbMbNbO%R?#MRs$08\B%YsRsPbPcPdPCPDPGPHPIPJPKPLPMPNPOPPPQPRPUPVPWPXPYPZP[P\PhNJ0720611RaP1P1%1?#3#2#2#JR?,ADR`PDC\%GaRp3?Rt@02UgP_PfP`PZP]P^PgPhPiPjPk1>AoRoPlPmPnM<{CIP_Pe%1<Rx#3#2#1#3#2#J,ADg02@VRyg02M8#0Rz#0R{#0R|#0#w#vR}/Nn%GyR~3?CIP_fBS0>%2r#2#J,AD%u}#8#8#8#8#8#8#8/Nn=?y~CIp,5HS_P1PbPcPdPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^MOtP_Q00PC1>A`R`PEPFfVR]fUR\fTR[%1>#3#1#9,>AR>%1x#;#;#;#;#;#;#;#9,>ARZPmPnP7P8P^fSRYfRRWfQRQPIPoPo1>AXRXPMPNPOPPPoPRfPRLfORKfNRJfMRHMOqPS%3<#2#2#2#1#3#W#3#1#2#2#9,>ARAPT%UBRGfDRd%p_R_FTRcPcg02IBRbPBPBPBPBPBPB%oBR~PBPHP~16BYP~G7PBP[PBP~PBPNP~D416BEPBPBP~PBPoP~D4RoPBPnPBP~PBPRP~D4D4G7PBPCPBPBPBP~PBPQP~D4PBPZPBP~PBPPP~D416B]PBPBP~PBPXP~16B8PBP~PBPKP~D4G7G7PGPBPBPBPBP~PBPWP~16B>PBP~PBPOP~D4G7PBPFPBPoPBP7PBP~PBPLP~D4D416B`PBPBPBP~PBPIP~D4PBPmPo16B\PBPBP~PBPMP~16B^PBP~PBPJP~D4G7G7G7G7PSPAPTPGPdP_FT'LADbcceP0PCP]P\P[PmPnP7P8P^PYPWPQPIPMPNPOPPPRPLPKPJPHPdfCQ0>PePfPgPhPiPjPkPlP9PtP1P1PVPDC\=?apRpPUPd15V01=0D':#m/:wQ01Q02Q03Q04Q05Q06Q07Q08p-0Rd1H1|1H1{1H1z5X15X1g02MW'l=?vuQ09P11O16P21O1;CsQ0:P@1E1xRx1E1=R='C,<@P1P=Q0;1E1<R<CF,<@Ru5@@,P@P@P3P4P4P5P9Ek5@@%U4RvP@%3q#2#1#2#2#2#9Rq,B19x1<,Cx,<@Pv1B1?9y1</C=,<@=@@u,P@P@P3P4P4P5Dz5@@C[C[Q0<Q0=b2b4b5X61X71X81W315621=20':g02WDR@[/:;1}2q,5;1A6?/5;1=;6':P@[/:w[[^61^71^81^3dP0PwPVP8PDP9p,2LOO6b1bHbIbJbKUX911Zp01Zt2[^91e1~tpeP:J00P;P6P2fFOWJ01b@WCW;W=W?W<XSBXRBXQBXPBXYsXVsWWXTBXUBX\BX[BXhBX]BXZBWXOCbAWBWDWFW:W>WEbGXdBXcBXbBXaBX`BX_BX^BXgBXfBWeo"). Qed.

End PrintfCore.


(* [comment removed for export] *)
Theorem printf_core_proof : forall (St : Type) (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
    (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z),
  sink_frame_stmt Fp B BS SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK -> out_stmt Fp B BS SINK TOPOK OUT ->
  printf_core_stmt Fp B BS SINK TOPOK OUT OUTFP.
Proof.
  intros St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary fmt VA i slots args
         HS BY HF Ha0 APC VAA Hi AOK FPC ST LO GLO SPHI TQ SSP MI FRM HA BS0 SEPF SEPB HAP HVA VAHI.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  pose proof (L_CORE2 Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) VA slots a3 a4 HF LO GLO SPHI TQ FRM HA SEPF SEPB HAP HVA (proj1 Ra1) VAHI BS0
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 st i args HS ST MI BY VAA SSP APC Hi AOK FPC) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply implM_mono.
  { apply C; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; lia. }
  cbv beta. intros r st' ms' P. unfold POST, W in P. unfold printf_core_post, SR.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & apv & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & HS' & SSP' & APC' & Hr).
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', apv, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact Hr.
Qed.

Theorem printf_core1_proof : printf_core1_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core ()) [] "p'0h02m'h12t6h22t5h32t4h42t3h52a7h62a6h72a5h82a4h92a3h:2a2h;2a1h<2t2h=2t1h>2t0h?1Hh@4__x1hA7__arithhB4__ffhC8__varmaphD5__withE1ChF4__p1hG1bhH3ms'hI4__x2hJ2a0hK4A2HIhL2BYhM1FhN3GLOhO2HAhP3HAPhQ2HFhR3Ha0hS2LOhT2MIhU3MI'hV2MUhW1PhX2P1hY3Ra1hZ3Ra2h[4SPHIh\3SSPh]4SSP'h^2STh_3ST'h`2WMha2b1hb2b2hc2b3hd2b4he2b5hf2b6hg2b7hh1chi6canaryhj2fchk3fmthl2gphm2lohn1mho2rahp2s0hq2s1hr3s10hs3s11ht2s2hu2s3hv2s4hw2s5hx2s6hy2s7hz2s8h{2s9h|2sph}2tph~3x28i003x29i013x30i023x31i032x5i042x6i052x7i061xp%0p%1p&0p;1p;2p;4p;3p;Ep;Op;7p;fp;Fp;6p;Gp;8g019Nj1>Tg01:3j1TTg01:Qj1aTg01IZj1LTg005mk20?Tg01[Mk109Tg01;4j1kTg02\0j22Tg01=Oj1}Tg0281j4fTg01J\j2:Tg01@Ej1BTg01I>j2STg01[2S00j2;Tg01H]k30FTg02Ocj1OTg01A]j25Tg01YGj3NTg01gKj2WTg01J?j2hTg01?Fj2=Tg02]Jk200Tg01A@j2CTg02n]lEjlFzTg01NTlO1Tg01OFj1rTg01Ohj1vTg02_Lj2uTg02`?j1tTg01C8j1ZTg01Sdj2eTg01fJk10JTg02>;k40ITg01TBk10HTg01T`k10GTg01UKj2sTg01fhk30ETg01W_k20>Tg01XAj2qTg01X[k20=Tg01Yak30<Tg01Z@k40;Tg02:Oj3pTg02?=k70:Tg01d[k208Tg02`hk307Tg01VQj2mTg02ohmf06Tg01>Jj3PTg02PdlFRmG02Tg02aCj1\Tg02bFj6^Tg01Paj74Tg01Unk305Tg030hk404Tg0324k103Tg01EWk201Tg02e8S01j20Tg02f<j19Tg01^Qj3MTg02j9j4QTg0076j6]Tg02jTj4`Tg032ej6yTg027?j4XTg01<[j2xTg01cjj3wTg01W4k40@Tg02;2k70ATg02<:k80BTg02;Vk70CTg02>Yk60DTg01]Qj4[Tg01^1j3bTg02<^j3dTf0R0#>#>p=Dg02L8R1g02LXR27N0p=Jg02?aR3f2R4f1R5P0CXp=V%L0#Lp=_1x30p=A%>0#>#>#>p=H%L0#>p=?f7R6f6R7f5R8f4R9f3R:P4P5P0F45w3p=F%>0#Lp=Gg02B^R;/m0p=KP4g02C<R<g02C[R=P=g02D;R>P;P5g02D[P0H0@g02EBK0Ap=EP:P<P=P=P>P4P5P0L0Bp=YP4P<P=P=P>P5P0K0Cp=oP5P<P=P=P>P0J0Dp=nP7P8%99P:P4P5P0F4p=8P;P;P4P5C[=b:0p=6Ad367P3P9P:P4CX1=50';,;8';p=3g02IBS02?N89AM:45/;0';p=7P;P;P8P9C[=b7:?M45/;0p=@Q02?N45/;0p=<Q02P7P8P9P:P4P5P0F47N6p=gP3P:P4P5CX/;0,;9p=UAM89:Ad345/;0';p=iP;P;P5P0C[p=~Ab9:4?M50p=|Ad350p=cP3P:P4P5CX/;0p=lQ02?N50p={P7P8P9P:P4P5P0C`C`p=Ig02G^R?#>R@#DRA#DRB#>RC#TRD#aRE%L@RF#T00?E%TB#a%TA#a$09\ERB%k;P3P:fJS03,2D%}0Cfg02AKRG/:0S04%DC#B,S0';Xh;>0F;5%O4#JfNRH15DGRI5NEfWRJ,2DRK9V67fXRL,2DRMg02jnRN'W,:6g02l0ROf8RP':fZS05,2DRQ%B@RR%LF#_#B'h'Sf;RSf9RT'=f<RU#AS06fTRV,2DRWf:RX-00;'Cg02m1':f^S07,2DRY/:WfURW,2D%BARA'C%BC,hRRC':PEPIfbRZfaR[f`R\f_S08f[R]Q05fQR^fPR_fOR`PHfMS09fLS0:fKS0;Q03fIRafHS0<fCS0=fBS0>f@S0?f?S0@fAS0AMEjPZP[P\Q08Q07f]Rbf\S0BP]Q05P0PLPJfVRcPWPVfSRdfRReP^P_P`PHQ09Q0:Q0;Q03PaQ0<fGS0CfFRffERgfDS0DMO1Q0=%>?#D#H#?#D#?#H#B,5DRhQ0>%rERiQ0A%v3RjGFXJE1uDJRk1:GK%tD,SK';RKPkPK%>?#G#?#G#D#?#_#?#D#BRKPGPGfcRk12DZRlP[P\Q0BP]PeP^P_P`PHQ09Q0:Q0;Q03PaQ0DQ0=Q0>Q0AQ0?fYRm,2DRnQ0@PM1CMARM%ZERoPJPcf=Rpg02JeRq#ZRr%kqRqP;1e;4P5&0J;RsH0I&0H;Rt&0G;Ru1s;?Rv1s;@%DF#G#D#H#BRF#K60E;5EuR@%r=RwP@CY20>u>R@P0P41q1220=04#JdB0<;G5H0;R2bBbCbDX@;XI;1W5F,:01W4F,:5[^@;^I;P012DkRFQ0>PXO3bAQ0A1WlN':ePrPq1e;5RlPtPu%G?#?#G#H#H#H#BRN#K=EuvR1PwP1CYP@P2bBbCbDX@;1:N01:N5[^@;P0Q0>PTO2bAQ0A,:OeP6P9p-0ROPrPqPsPtPuP<P=P=P>%KKR>=Eu>%L?#?#?#D#BR=#K9p;>%G?#G#_#?#?#?#?#H#BR?#K5Eu5ou1nu4K0:P@P2bBbCbDWF1:KK1CK=R=/:?';0080^FOP01CnAR?/:K1:=?';O1bAP:PrPqPlPt%KA9p;vR==Eu=P@P2bBbCbDX@;1C0ARK/:K^@;P0PnO1bA1:Gn1SnC<075PrPqPsPt1m;GRs=EusP@P2bBbCbD1:GGP0bAQ08Q07PbPWPVPdQ0<Q0CPfPgPXP8f>RnNf06Q0>?PMoQ0=Q0A'=Q0A#O#JffRMfeR>,2DR<fdRNPkQ08Q07PWPVPdPeP^P_P`PHQ09Q0:Q0CPfPgQ0DQ0=PGMFRPM15D<PNPkPZP[P\Q08Q07PIQ0B,2DR<,5DR112D]Rx,5DRyQ05PmPLPJPcPWPVPdPeP^P_P`PHQ09Q0:Q0;Q03PaQ0<MO1Q0CPhPfPiPgPjGF[[[PE15DFQ0D1CQA;PoRQQ0=,=gRFQ0=#O#JRzfhR{fgR|,2DS0EPMP>P[P\PJPcPWPVPdPeP^P_P`PHPaQ0<Q0CPfPgPGMFRS0FP{P:PMP>PNPkPZP[P\PI15DYS0G12DbRY,5DR}Q0BP]Q05PmPLPJPcPWPVPdPeP^P_P`PHQ09Q0:Q0;Q03MO1PaPhQ0<PiQ0CPjGF[[[XGEP0Pk%\kE^Q0=?P?oQ0DQ0>'=Q0>#O#JP|12DMP>PNP\Q08PcPWPVPdPeP^P_P`PHQ09Q0<Q0CPfPgQ0DPGMFRS0HP|PMP>PNPkPZP[P\Q08PIP}P1P]Q05PmPLPJPcPWPVPdPeP^P_P`PHQ09Q0:Q0;Q03PaMO1Q0<PhQ0CPiPfPjGF[[[PEPy1CxA=PgoRxQ0D,=fR1Q0D#O#JR?fiR~12D{P|PMPZP[PLPJPcPWPVPdPeP^P_P`Q03PaQ0<Q0CPfPGMFRS0IP~P{P|PMP>PNPkPZP[PIP:Q0GPbQ0BP]Q05PmPLPJPcPWPVPdPeP^P_P`PHQ09Q0:Q0;MO1Q03PhPaPiQ0<PjGF[[[XGEP0P]%\]S0GE^Q0FP{P|PMP>PNPkPZP[P\PIQ07P}Q0BP]Q05PmPLPJPcPWPVPdPeP^P_P`PHQ09Q0:Q0;Q03MO1PaPhQ0<PiQ0CPjGF\z\F\QPEPy1C<AR<=PfoRyQ0C/=g%Og#JfjS0F12D~P{P|PkPZPmPLPJPcPWPVPdPeP^P_Q0;Q03PaQ0<Q0CPGMFRQ0FP~P{P|PMP>PNPkPZPIP\P:Q07PbQ0BP]Q05PmPLPJPcPWPVPdPeP^P_P`PHQ09Q0:MO1Q0;PhQ03PiPaPjGF[[[XGEP0P]Q0GE^Q0IP~P{P|PMP>PNPkPZP[PIQ08Q07PbQ0BP]Q05PmPLPJPcPWPVPdPeP^P_P`PHQ09Q0:Q0;MO1Q03PhPaPiQ0<PjGF\?\1\xP3Q0HP|PMP>PNP\Q08PcPWPVPdPeP^P_P`PHQ09Q0<Q0CPgQ0DPfMEjP|PMP>PNPkPZP[P\Q08PIPbQ0BP]Q05PmPLPJPcPWPVPdPeP^P_P`PHQ09Q0:Q0;Q03PaMO1Q0<PhQ0CPiPfPjF4P0PfP<PrPqPlPtPuAEusv1nu:5ouPwAEus=CYP@P2bBbCbDX@;XFOQ04/;51C5ARA,:G[^@;^FOP01SYCPYP8O3bAPrPqPlPtPu%KR>05;D9Eu=R=PwP=CYP@P2bBbCbDX@;1:KC1:AC[^@;P0PYP6O2bAH04P3PfP<&03oCfePyePXQ0?O3Q02P{Q0EPMP>P[P\PJPcPWPVPdPeP^P_P`PHPaQ0<Q0CPfPgPGP0NG02S0EQ01PEQ0?fxRGfwS04,2DRy,5DfvRofuS0HPnPpPUfqS0IfpS0GPIPSPXPTPPP6P7P8P|PMP>PNPkPZP[P\Q08Q07P9P:P4P5MO1PmPGPLPiP0PjF8201;;R<PcPy%Z<R3C6PJP0PJP0%A0RYP0PcPyP0PWG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>EQ0AfyRyPGQ04PoPnPpPUfrS0JQ0IPIPSPXPTPPP6P7P8P{P|PMP>PNPkPZP[P\Q08P9P:P4P5MO1Q05PyPmPiP0PjF8P<PJ12DGRAP3C6PLP0PLP0PYP0PJPAP0PcG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0Q0>fzRA12DyRC,5DPGQ04PnPpPUfsS0KQ0JPIPSPXPTPPP6P7P8P~P{P|PMP>PNPkPZP[P\P9P:P4P5MO1P]PAQ05PiP0PjF8P<PLPCP3C6PmP0PmP0PYP0PLPCP0PJG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EQ01PEQ0=f{RC12DARK,5DPyPGQ0@PpPUftS0LQ0KPIPSPXPTPPP6P7P8Q0FP~P{P|PMP>PNPkPZP[P9P:P4P5MO1Q0BPCP]PiP0PjF8P<PmPKP3C6Q05P0Q05P0PYP0PmPKP0PLG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=Ef}RKf|R2PCPAPnPpPUPoQ0HPIPSPXPTPPP6P7P8flS0MfkS0NQ0FP~P{P|PMP>PNPkP9P:P4P5MO1Q07%9KR@PbPiP0PjF4P<P]12D2R=P3Q0BP0Q0BP0PYP0P]P=P0Q05G3F@Rw5<gX0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0PK15D=PCPAQ0APpPUPoQ0HPIPSPXPTPPP6P7P8Q0MQ0NQ0FP~P{P|PMP>PNPkP9P:P4P5MO1Q07P@PbPiP0PjF4=<gwX0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EQ01PEPff~Rw12DKR@,5DP2PCQ0>PnPUQ04PoPIPSPXPTPPP6P7P8fmS0OQ0MQ0NQ0FP~P{P|PMP>PNP9P:P4P5MO1Q08PwQ07PiP0PjF8P<Q0BP@P3C6PbP0PbP0PYP0Q0BP@P0P]G3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<Ep+01BR@p+01AR=p+01@RuPwPnPpPUPAPyPIPSPXPTPPP6P7P8Q0GfoS0PfnS0QQ0OQ0MQ0NQ0FP~P{P|P9P:P4P5MO1PZ%9@RRP[PiP0PjF4P<Q0812D=RtP3P\P0P\P0PYP0Q08PtP0Q07G3F@Rl5<aX0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0Q0<P=12DuRq,5DPwPKQ0DQ0?PUPyPGPIPSPXPTPPP6P7P8Q0PQ0QQ0OQ0MQ0NQ0FP~P{P|PMP9P:P4P5MO1P[P=P\PiP0PjF8P<Q07PqP3C6Q08P0Q08P0PYP0Q07PqP0PbG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EQ01PEP@15DtPuPwPgQ0APpPAPyPIPSPXPTPPP6P7P8Q0GQ0PQ0QQ0OQ0MQ0NQ0FP~P{P|P9P:P4P5MO1PZPRP[PiP0PjF4=<alX0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;EQ09p+01FS0Rp+01ERlp+01DRRp+01CRtPnPpPUPwPKPIPSPXPTPPP6P7P8Q0LQ0KQ0JQ0IQ0GQ0PQ0QQ0OQ0MQ0NP9P:P4P5MO1PMQ0RP>PiP0PjF8P<Pk12DlRqP3C6PNP0PNP0PYP0PkPqP0PZG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0Q0;PR12DtRq,5DP@P=Q0CQ0=Q0@P2PCPIPSPXPTPPP6P7P8Q0JQ0IQ0GQ0PQ0QQ0OQ0MQ0NQ0FP~P9P:P4P5MO1PNPRPkPiP0PjF8P<P[PqP3C6PZP0PZP0PYP0P[PqP0P\G3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EQ01PEQ0:Pl12DRRq,5DPtP@Q0<Q0DQ0?PKP2PIPUPXPTPPP6P7P8Q0KQ0JQ0IQ0GQ0PQ0QQ0OQ0MQ0NQ0FP9P:P4P5MO1P>PlPNPiP0PjF8P<PZPqP3C6PkP0PkP0PYP0PZPqP0P[G3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:Ep+01JS0Sp+01IRqp+01HS0Tp+01GS0UPnPpPUPtP@PIPSPXPTPPP6P7P8PGQ04PoQ0HQ0LQ0KQ0JQ0IQ0GQ0PP9P:P4P5MO1Q0FQ0S#9RrP~PiP0PjF4P<P|12DqROP3P{P0P{P0PYP0P|POP0PMG3F@Rs5<^X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0PHQ0UQ0R,2DRv,5DPlPRQ03PfQ0>PuPwPIPnPXPTPPP6P7P8Q0HQ0LQ0KQ0JQ0IQ0GQ0PQ0QQ0OQ0MP9P:P4P5MO1P|Q0UPMPiP0PjF8P<PNPvP3C6P>P0P>P0PYP0PNPvP0PkG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EQ01PEP`Q0TQ0U,2DRv,5DQ0RPlQ0;Q0CQ0=P=PuPIQ0@PSPTPPP6P7P8PoQ0HQ0LQ0KQ0JQ0IQ0GQ0PQ0QQ0OP9P:P4P5MO1P{Q0TP|PiP0PjF8P<P>PvP3C6PMP0PMP0PYP0P>PvP0PNG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9Ep+01NS0Vp+01MS0Wp+01LS0Xp+01KS0YPnPpPUQ0UQ0RPIPSPXPTPPP6P7P8P2PCPAPyPGQ04PoQ0HQ0LQ0KP9P:P4P5MO1Q0QQ0V#9RvQ0OPiP0PjF4P<Q0NQ0W,2DRhP3Q0MP0Q0MP0PYP0Q0NPhP0Q0FG3F@Rx5<WX0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0Q0S15DOQ0TQ0UQ09PaPgPtP@PIQ0APpPTPPP6P7P8PGQ04PoQ0HQ0LQ0KQ0JQ0IQ0GQ0PP9P:P4P5MO1Q0FPrP~PiP0PjF4=<^sX0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EQ01PEPeQ0YQ0S,2DRs,5DPqQ0TPHQ03PfPRPtPIQ0>PnPXPPP6P7P8PyPGQ04PoQ0HQ0LQ0KQ0JQ0IQ0GP9P:P4P5MO1Q0NQ0YQ0FPiP0PjF8P<P{PsP3C6P~P0P~P0PYP0P{PsP0P|G3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8EPmp+01RS0Zp+01QS0[p+01PS0\p+01OS0]PnPpPUQ0YQ0SPIPSPXPTPPP6P7P8P=PuPwPKP2PCPAPyPGQ04P9P:P4P5MO1Q0JQ0ZQ0IPiP0PjF8P<Q0PQ0[,2DRsP3C6Q0GP0Q0GP0PYP0Q0PPsP0Q0QG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0PVQ0WQ0X,2DRs,5DQ0YQ0SP_Q0:Q0<Q0RPlPIQ0DQ0?PUPPP6P7P8PCPAPyPGQ04PoQ0HQ0LQ0KQ0JP9P:P4P5MO1Q0OQ0WQ0MPiP0PjF8P<Q0FPsP3C6Q0NP0Q0NP0PYP0Q0FPsP0P~G3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EQ01PEQ0V15DhQ0XQ0YP^Q09PaQ0UQ0RPIPgQ0APpPTP6P7P8P2PCPAPyPGQ04PoQ0HQ0LQ0KP9P:P4P5MO1Q0QPvQ0OPiP0PjF4=<WxX0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7Ep+01VS0^p+01US0_p+01TS0`p+01SS0aPnPpPUQ0]Q0VPIPSPXPTPPP6P7P8PlPRPtP@P=PuPwPKP2PCP9P:P4P5MO1PoQ0^#9RxQ0HPiP0PjF4P<Q0KQ0_,2DRvP3Q0LP0Q0LP0PYP0Q0KPvP0Q0JG3F@Rh5<bX0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0PJQ0\Q0],2DRs,5DQ0VQ0WPdP`Q0;PqQ0TPIQ0CQ0=Q0@PSP6P7P8PwPKP2PCPAPyPGQ04PoQ0HP9P:P4P5MO1Q0GQ0\Q0PPiP0PjF8P<Q0OPsP3C6Q0QP0Q0QP0PYP0Q0OPsP0Q0MG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EQ01PEPLQ0[Q0\,2DRs,5DQ0]Q0VPVP_Q0:Q0SPqPIQ0<Q0DQ0?PUPPP7P8PuPwPKP2PCPAPyPGQ04PoP9P:P4P5MO1Q0IQ0[Q0GPiP0PjF8P<Q0QPsP3C6Q0PP0Q0PP0PYP0Q0QPsP0Q0OG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6Ep+01ZS0bp+01YS0cp+01XS0dp+01WS0ePnPpPUQ0aQ0ZPIPSPXPTPPP6P7P8PqQ0TQ0UQ0RPlPRPtP@P=PuP9P:P4P5MO1PAQ0b#9RsPyPiP0PjF4P<Q04Q0c,2DRrP3PGP0PGP0PYP0Q04PrP0PoG3F@RO5<[X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0Q05Q0aQ0Z,2DR1,5DQ0[Q0\PcPePHQ0XQ0YPIQ03PfQ0>PnPXP7P8P@P=PuPwPKP2PCPAPyPGP9P:P4P5MO1Q0KQ0aQ0JPiP0PjF8P<Q0GP1P3C6Q0IP0Q0IP0PYP0Q0GP1P0Q0PG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EQ01PEP]Q0`Q0a,2DR1,5DQ0ZQ0[PJPdP`Q0WQ0XPIQ0;Q0CQ0=Q0@PSP6P8PtP@P=PuPwPKP2PCPAPyP9P:P4P5MO1Q0LQ0`Q0KPiP0PjF8P<Q0IP1P3C6Q0JP0Q0JP0PYP0Q0IP1P0Q0GG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5EP>p+01^S0fp+01]S0gp+01\S0hp+01[S0iPnPpPUQ0eQ0^PIPSPXPTPPP6P7P8Q0WQ0XQ0YQ0SPqQ0TQ0UQ0RPlPRP9P:P4P5MO1PwQ0fPKPiP0PjF8P<PCQ0g,2DR1P3C6P2P0P2P0PYP0PCP1P0PAG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0Q0^15DvQ0`Q0aPmPWP^Q0]Q0VPIQ09PaPgQ0APpPTP8PlPRPtP@P=PuPwPKP2PCP9P:P4P5MO1PoPxQ0HPiP0PjF4=<bhX0B,0BX1E,0EX2E,0EX3E,0EX4E,0EQ01PEQ07Q0eQ0^,2DRh,5DQ0_Q0`Q05PcPeQ0\Q0]PIPHQ03PfQ0>PnPXP7Q0RPlPRPtP@P=PuPwPKP2P9P:P4P5MO1Q04Q0ePoPiP0PjF8P<Q0LPhP3C6Q0HP0Q0HP0PYP0Q0LPhP0Q0KG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4Ep+01bRhp+01aS0jp+01`S0kp+01_S0lPnPpPUQ0iQ0bPIPSPXPTPPP6P7P8Q0[Q0\Q0]Q0VQ0WQ0XQ0YQ0SPqQ0TP9P:P4P5MO1Pt%9hS0mP@PiP0PjF4P<PuQ0j,2DS0nP3P=P0P=P0PYP0PuQ0nP0PwG3F@S0o5<~X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0P\Q0cQ0d,2DRx,5DQ0eQ0^Q0BPLPVQ0ZQ0[PIP_Q0:Q0<Q0DQ0?PUPPQ0TQ0UQ0RPlPRPtP@P=PuPwP9P:P4P5MO1PyQ0cPGPiP0PjF8P<PoPxP3C6Q04P0Q04P0PYP0PoPxP0Q0HG3E7X0B,0BX1E,0EX2E,0EX3E,0EQ01PEQ0b15DrQ0dQ0ePbPmPWQ0aQ0ZPIP^Q09PaPgQ0APpPTPqQ0TQ0UQ0RPlPRPtP@P=PuP8P:P4P5MO1PAPsPyPiP0PjF4=<[OX0B,0BX1E,0EX2E,0EX3EQ0Op+01fROp+01eRsp+01dRrp+01cRxPnPpPUQ0lQ0fPIPSPXPTPPP6P7P8Q0_Q0`Q0aQ0ZQ0[Q0\Q0]Q0VQ0WQ0XP9P:P4P5MO1Q0U%9OS0pQ0RPiP0PjF4P<PR12DsS0qP3C6S0rPlP0PlP0PYP0PRQ0qP0PtG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0PkQ0hQ0i,2DRv,5DQ0bQ0cQ08P]PJQ0_Q0`PIPdP`Q0;Q0CQ0=Q0@PSQ0YQ0SPqQ0TQ0UQ0RPlPRPtP@P6P:P4P5MO1P2Q0hPCPiP0PjF8P<PyPvP3C6PAP0PAP0PYP0PyPvP0PGG3E7X0B,0BX1E,0EX2E,0EQ01PEPNQ0gQ0h,2DRv,5DQ0iQ0bP\Q0BPLQ0^Q0_PIPVP_Q0:Q0<Q0DQ0?PUQ0XQ0YQ0SPqQ0TQ0UQ0RPlPRPtPPP9P4P5MO1PKQ0gP2PiP0PjF8P<PAPvP3C6PCP0PCP0PYP0PAPvP0PyG3E7X0B,0BX1E,0EX2EQ0Ip+01jRvp+01iR1p+01hR?p+01gRQPnPpPUPxPhPIPSPXPTPPP6P7P8Q0cQ0dQ0eQ0^Q0_Q0`Q0aQ0ZQ0[Q0\P9P:P4P5MO1Q0YPvQ0SPiP0PjF8P<Q0T12D1S0sP3C6S0tPqP0PqP0PYP0Q0TQ0sP0Q0UG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0PMQ0lQ0f,2DRF,5DQ0gQ0hPZQ07Q05Q0dQ0ePIPcPePHQ03PfQ0>PnQ0VQ0WQ0XQ0YQ0SPqQ0TQ0UQ0RPlPXP7P4P5MO1PuQ0lPwPiP0PjF8P<P2PFP3C6PKP0PKP0PYP0P2PFP0PCG3E7X0B,0BX1E,0EQ01PEP|Q0kQ0l,2DRF,5DQ0fQ0gPkQ08P]Q0cQ0dPIPJPdP`Q0;Q0CQ0=Q0@Q0]Q0VQ0WQ0XQ0YQ0SPqQ0TQ0UQ0RPSP6P:P5MO1P=Q0kPuPiP0PjF8P<PKPFP3C6PwP0PwP0PYP0PKPFP0P2G3E7X0B,0BX1EQ0Hp+01nS0up+01mRFp+01lRzp+01kR}PnPpPUPQPOPIPSPXPTPPP6P7P8Q0gQ0hQ0iQ0bQ0cQ0dQ0eQ0^Q0_Q0`P9P:P4P5MO1Q0]Q0uQ0VPiP0PjF8P<Q0X12DFS0vP3C6Q0WP0Q0WP0PYP0Q0XQ0vP0Q0YG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0PhQ0n,5DQ0kQ0lP>P[PbQ0iQ0bPIPmPWP^Q09PaPgQ0AQ0[Q0\Q0]Q0VQ0WQ0XQ0YQ0SPqQ0TPpPTP8P5MO1PtQ0mP@PiP0PjF4Q0o5<~X0B,0BQ01PBQ0FPx12DhS01,5DQ0jQ0kPMPZQ07Q0hQ0iPIQ05PcPePHQ03PfQ0>Q0ZQ0[Q0\Q0]Q0VQ0WQ0XQ0YQ0SPqPnPXP7P4MO1PRPxPtPiP0PjF8P<P=Q01P3C6P@P0P@P0PYP0P=Q01P0PuG3E7X0BPyp+022S01p+021S0>p+020S0op+01oS0mPnPpPUP}PvPIPSPXPTPPP6P7P8Q0jQ0kQ0lQ0fQ0gQ0hQ0iQ0bQ0cQ0dP9P:P4P5MO1Q0aQ01Q0ZPiP0PjF8P<Q0\Q0>,2DS0nP3C6Q0[P0Q0[P0PYP0Q0\Q0nP0Q0]G3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0Q0MPs12DrS0w,5DPxPhP{PNP\Q0fQ0gPIQ0BPLPVP_Q0:Q0<Q0DQ0`Q0aQ0ZQ0[Q0\Q0]Q0VQ0WQ0XQ0YQ0?PUPPP9MO1Q0RPsPlPiP0PjF8P<PtQ0wP3C6PRP0PRP0PYP0PtQ0wP0P@G3E7Q00Q0OPOQ0q,5DPrPxP~P>P[Q0lQ0fPIPbPmPWP^Q09PaPgQ0_Q0`Q0aQ0ZQ0[Q0\Q0]Q0VQ0WQ0XQ0APpPTP8MO1Q0UQ0pQ0RPiP5PjGgQ0rPlP5PlP5%A5P5PRQ0q1=5tDUEiPKp+026S0qp+025S0rp+024S0pp+023S0wPnPpPUQ0mQ0uPIPSPXPTPPP6P7P8PsPrPxPhQ0jQ0kQ0lQ0fQ0gQ0hP9P:P4P5MO1Q0eQ0qQ0^PiP0PjF8P<Q0`Q0r,2DS0xP3C6Q0_P0Q0_P0PYP0Q0`Q0xP0Q0aG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0Q0PP?12DQ,5DPOPsQ0NP|PkQ0jQ0kPIQ08P]PJPdP`Q0;Q0CQ0eQ0^Q0_Q0`Q0aQ0ZQ0[Q0\Q0]Q0VQ0=Q0@PSP6MO1Pq%9?Q0TPiP:PjGgQ02P112D?S0y,5DPQPOQ0MP{PNPhQ0jPIP\Q0BPLPVP_Q0:Q0<Q0dQ0eQ0^Q0_Q0`Q0aQ0ZQ0[Q0\Q0]Q0DQ0?PUPPMO1Q0SP1PqPiP9PjF8Q02Q0t?Mq8S0tPqP8%A8P8Q0TQ0sP8Q0UG3S0s';Q0?p+02:S0[p+029S0_p+028S0zp+027S0{PnPpPUQ0wQ01PIPSPXPTPPP6P7P8P1P?PQPOPsPrPxPhQ0jQ0kP9P:P4P5MO1Q0iQ0[#9S0|Q0bPiP0PjF4S0}P<Q0dQ0_,2DS0~P3C6S10Q0cP0Q0cP0PYP0Q0dQ0~Q0e,=0DUEiS113<X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0E[WHP<Q0UQ0yP3Q0TP9Q0TP9%A9P9Q0UQ0yP9Q0RG3F@Q00Q0tQ0sQ0[Q0~,5DS0sQ0zQ0{PKPyQ0HQ0wQ01PIQ0IQ0OP~P>P[PbPmP1P?PQPOPsPrPxPhQ0jQ0kPWP^Q09PaMO1Q0iQ0|Q0bPiPgPjF4Q0}Q113<X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0P<Q0S12D}'~P3Q0YP6D|Q0XPP%APPPQ0Y12DzPPQ0SG3Q00Q0W/cT%ATPTQ0XQ0vQ0Y,=TDUp+02>S0vp+02=S11,2DS0},5Dp+02<S0tp+02;S0yP@PKPyQ0{Q0qPIQ0HQ0IQ0OP~P>P[PbPFPzP}PvP1P?PQPOPsPrPmPWP^Q09MO1Q0lQ0v#9S12Q0fPiPaPjF4S13Q0vQ11Q0tQ0yPnPpPUQ0{Q0qPIPSPXPTPPP6P7P8PFPzP}PvP1P?PQPOPsPrP9P:P4P5MO1Q0lQ12Q0fPiP0PjF4P<Q0hQ0}P3Q0gP0Q0gP0PYP0Q0hQ0}P0Q0iG3F@S0}3<X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0Q0]/cSQ06PUQ0]Q0o,2DQ0V,=UDUQ00%ApPpQ0\Q0nQ0],=pClp+02BS0]p+02AS0n,2DS0\,5Dp+02@S0Vp+02?S06Q0RP@PKQ0yQ0[PIPyQ0HQ0IQ0OP~P>P[Q0>Q0oQ0mQ0uPFPzP}PvP1P?PbPmPWP^MO1PxQ0]#9S14PhPiQ09PjF4S15Q0]Q0nQ0VQ06PnPpPUQ0yQ0[PIPSPXPTPPP6P7P8Q0>Q0oQ0mQ0uPFPzP}PvP1P?P9P:P4P5MO1PxQ14PhPiP0PjF4P<Q0kQ0\P3Q0jP0Q0jP0PYP0Q0kQ0\P0Q0lG3F@S0\3<X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0Q0@#AQ0?Q0aQ0p,2DQ0?Q0Z'=ClQ00Q0AQ0`Q0x3VQ0AQ0a'=p+02FS0ap+02ES0A,2DS0x,5Dp+02DS0`p+02CS00Q0SQ0RP@Q06Q0vPIPKPyQ0HQ0IQ0OP~P>Q0rQ0pQ0wQ01Q0>Q0oQ0mQ0uPFPzP[PbPmPWMO1PQQ0a#9S0ZPOPiP^PjF4S0?Q0aQ0AQ0`Q00PnPpPUQ06Q0vPIPSPXPTPPP6P7P8Q0rQ0pQ0wQ01Q0>Q0oQ0mQ0uPFPzP9P:P4P5MO1PQQ0ZPOPiP0PjF4P<PrQ0xP3PsP0PsP0PYP0PrQ0xP0PxG3F@S0x3<X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>E,0EP0Q0=Q0^Q0{,2D3VQ0DQ0^'=PEp+02IS0^p+02HS0D,2DS0=,5Dp+02GS0@Q0aQ0WPqPlQ0]Q0nPIP=P2PGQ0LQ0GQ0MP{Q0zQ0{Q0qQ0rQ0pQ0wQ01Q0>Q0oQ0mPNP\Q0BPLMO1PvQ0^#9S0WP1PiPVPjF4Q0^Q0DQ0@Q0aPnPpPUQ0]Q0nPIPSPXPTPPP6P7P8Q0zQ0{Q0qQ0rQ0pQ0wQ01Q0>Q0oQ0mP9P:P4P5MO1PvQ0WP1PiP0PjF4P<PQQ0=P3C6P?P0P?P0PYP0PQQ0=P0POG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=E,0EX>EPKPEQ0DQ0@,2DRn,5DQ0aQ0AQ0XQ0TPRQ0nQ0VPIPuPCQ04Q0KQ0PQ0NP|Q0{Q0qQ0rQ0pQ0wQ01Q0>Q0oQ0mQ0uPkQ08P]PJMO1P1Q0D#9S0=P?PiPdPjF4Q0DQ0@Q0aQ0AQ0XPpPUQ0nQ0VPIPSPXPTPPP6P7P8Q0{Q0qQ0rQ0pQ0wQ01Q0>Q0oQ0mQ0uP9P:P4P5MO1P1Q0=P?PiP0PjF4P<POPnP3C6PQP0PQP0PYP0POPnP0PsG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<E,0EX=EPyPEQ0@Q0a,2DRn,5DQ0AQ0`Q0YQ0UPtQ0VQ06PIPwPAPoQ0JQ0QQ0FPMQ0qQ0rQ0pQ0wQ01Q0>Q0oQ0mQ0uPFPZQ07Q05PcMO1P?Q0@#9S0=PQPiPePjF4Q0@Q0aQ0AQ0`Q0YQ0UPUQ0VQ06PIPSPXPTPPP6P7P8Q0qQ0rQ0pQ0wQ01Q0>Q0oQ0mQ0uPFP9P:P4P5MO1P?Q0=PQPiP0PjF4P<PsPnP3C6POP0POP0PYP0PsPnP0PrG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;E,0EX<EQ0HPEQ0?Q0aQ0AQ0`Q00Q0SQ0RP@Q06Q0vPIPSPXPTPPP6P7P8Q0rQ0pQ0wQ01Q0>Q0oQ0mQ0uPFPzP9P:P4P5MO1PQQ0ZPOPiP0PjF4Q0x3<X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:E,0EX;EQ0IPEQ0AQ0`,2DRS,5DQ00Q0]PqPlP=Q0vQ11PIP2PGQ0LQ0GQ0MP{PNQ0pQ0wQ01Q0>Q0oQ0mQ0uPFPzP}P\Q0BPLPVMO1POQ0A#9RnPsPiP_PjF4Q0AQ0`Q00Q0]PqPlP=Q0vQ11PIP2PXPTPPP6P7P8Q0pQ0wQ01Q0>Q0oQ0mQ0uPFPzP}P9P:P4P5MO1POPnPsPiP0PjF4P<PxPSP3C6PrP0PrP0PYP0PxPSP0PhG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9E,0EX:EQ0OPEQ0`Q00,2DRS,5DQ0]Q0nQ0TPRPuQ11Q0tPIPCQ04Q0KQ0PQ0NP|PkQ0wQ01Q0>Q0oQ0mQ0uPFPzP}PvQ08P]PJPdMO1PsQ0`#9RnPrPiP`PjF4Q0`Q00Q0]Q0nQ0TPRPuQ11Q0tPIPCQ04PTPPP6P7P8Q0wQ01Q0>Q0oQ0mQ0uPFPzP}PvP9P:P4P5MO1PsPnPrPiP0PjF4P<PhPSP3C6PxP0PxP0PYP0PhPSP0Q0jG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8E,0EX9EP~PEQ00Q0],2DRS,5DQ0nQ0VQ0UPtPwQ0tQ0yPIPAPoQ0JQ0QQ0FPMPZQ01Q0>Q0oQ0mQ0uPFPzP}PvP1Q07Q05PcPeMO1PrQ00#9RnPxPiPHPjF4Q00Q0]Q0nQ0VQ0UPtPwQ0tQ0yPIPAPoQ0JPPP6P7P8Q01Q0>Q0oQ0mQ0uPFPzP}PvP1P9P:P4P5MO1PrPnPxPiP0PjF4P<Q0jPSP3C6PhP0PhP0PYP0Q0jPSP0Q0kG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7E,0EX8EP>PEQ15Q0]Q0nQ0VQ06Q0RP@PKQ0yQ0[PIPyQ0HQ0IQ0OP6P7P8Q0>Q0oQ0mQ0uPFPzP}PvP1P?P9P:P4P5MO1PxQ14PhPiP0PjF4Q0\3<X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6E,0EX7EP[PEQ0nQ0V,2DR6,5DQ06Q0vPlP=P2Q0[Q0_PIPGQ0LQ0GQ0MP{PNP\Q0oQ0mQ0uPFPzP}PvP1P?PQQ0BPLPVP_MO1PhQ0n#9RSQ0jPiQ0:PjF4Q0nQ0VQ06Q0vPlP=P2Q0[Q0_PIPGQ0LQ0GQ0MP{P7P8Q0oQ0mQ0uPFPzP}PvP1P?PQP9P:P4P5MO1PhPSQ0jPiP0PjF4P<Q0lP6P3C6Q0kP0Q0kP0PYP0Q0lP6P0Q0fG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5E,0EX6EPbPEQ0VQ06,2DR6,5DQ0vQ11PRPuPCQ0_Q0zPIQ04Q0KQ0PQ0NP|PkQ08Q0mQ0uPFPzP}PvP1P?PQPOP]PJPdP`MO1Q0jQ0V#9RSQ0kPiQ0;PjF4Q0VQ06Q0vQ11PRPuPCQ0_Q0zPIQ04Q0KQ0PQ0NP|PkP8Q0mQ0uPFPzP}PvP1P?PQPOP9P:P4P5MO1Q0jPSQ0kPiP0PjF4P<Q0fP6P3C6Q0lP0Q0lP0PYP0Q0fP6P0Q0gG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4E,0EX5EPmPEQ06Q0v,2DR6,5DQ11Q0tPtPwPAQ0zQ0{PIPoQ0JQ0QQ0FPMPZQ07Q0uPFPzP}PvP1P?PQPOPsQ05PcPePHMO1Q0kQ06#9RSQ0lPiQ03PjF4Q06Q0vQ11Q0tPtPwPAQ0zQ0{PIPoQ0JQ0QQ0FPMPZQ07Q0uPFPzP}PvP1P?PQPOPsP9P:P4P5MO1Q0kPSQ0lPiP0PjF4P<Q0gP6P3C6Q0fP0Q0fP0PYP0Q0gP6P0Q0hG3E7X0B,0BX1E,0EX2E,0EX3E,0EX4EPWPEQ13Q0vQ11Q0tQ0yP@PKPyQ0{Q0qPIQ0HQ0IQ0OP~P>P[PbPFPzP}PvP1P?PQPOPsPrPmP:P4P5MO1Q0lQ12Q0fPiP0PjF4Q0}3<X0B,0BX1E,0EX2E,0EX3EP^PEQ11Q0t,2DR:,5DQ0yQ0[P=P2PGQ0qQ0rPIQ0LQ0GQ0MP{PNP\Q0BPzP}PvP1P?PQPOPsPrPxPLPVP_Q0:MO1Q0fQ11#9RFQ0gPiQ0<PjF4Q11Q0tQ0yQ0[P=P2PGQ0qQ0rPIQ0LQ0GQ0MP{PNP\Q0BPzP}PvP1P?PQPOPsPrPxPLPVP4P5MO1Q0fPFQ0gPiP0PjF4P<Q0iP:P3C6Q0hP0Q0hP0PYP0Q0iP:P0Q0bG3E7X0B,0BX1E,0EX2EQ09PEQ0tQ0y,2DR:,5DQ0[Q0_PuPCQ04Q0rQ0pPIQ0KQ0PQ0NP|PkQ08P]P}PvP1P?PQPOPsPrPxPhPJPdP`Q0;MO1Q0gQ0t#9RFQ0hPiQ0CPjF4Q0tQ0yQ0[Q0_PuPCQ04Q0rQ0pPIQ0KQ0PQ0NP|PkQ08P]P}PvP1P?PQPOPsPrPxPhPJPdP`P5MO1Q0gPFQ0hPiP0PjF4P<Q0bP:P3C6Q0iP0Q0iP0PYP0Q0bP:P0Q0cG3E7X0B,0BX1EPaPBQ0yQ0[,2DR:,5DQ0_Q0zPwPAPoQ0pQ0wPIQ0JQ0QQ0FPMPZQ07Q05PvP1P?PQPOPsPrPxPhQ0jPcPePHQ03MO1Q0hQ0y#9RDQ0iPiPfPjF4Q0yQ0[Q0_Q0zPwPAPoQ0pQ0wPIQ0JQ0QQ0FPMPZQ07Q05PvP1P?PQPOPsPrPxPhQ0jPcPePHQ03MO1RFQ0hPDQ0iPiP0PjF4P<Q0cP:P3C6R3Q0bP0Q0bP0PYP0Q0cP:P0Q0dG3E7X0BPgPEQ0_Q0yP0Q0_Q0zPwPAPoQ0pQ0wPIQ0JQ0QQ0FPMPZQ07Q05PvP1P?PQPOPsPrPxPhQ0jPcPePHQ03MO1Q0hPDQ0iPiPfPjF4PFQ0hPDQ0iPiPfPjF4P3Q0bPfQ0bPf%AfPfQ0cP:PfQ0dG3E7XGEQ0[Q0_Q0zQ0{PKPyQ0HQ0wQ01PIQ0IQ0OP~P>P[PbPmP1P?PQPOPsPrPxPhQ0jQ0kPWP^Q09PaMO1Q0iQ0|Q0bPiPgPjF4Rj/{jQ10Q0c;MgRiQ0c/cgRh%AgRxQ0dQ0~5VgRrQ0e,=gRg';Rs';RO';RQ';Q02/qjPiPQPpPhPOPTPxPsP8PrPgP5P0CQCQCQCQCQQ0sQ0_#\E]C`FIFIFIFIFIFIFIW]W_P5P0O2n2001000010121000000W?WUP5P0O2n2001000010121000000W?W`P5P0O2n2001000010121000000W?WVP5P0O2n2001000010121000000W?Q0GP0E]W?P5P0O2n2001000010121000000W?X0BP5P0O2n2001000010121106000W?Z02EP5P0O2n2001000010121106000W?Z01EP5P0O2n2011000010121106000W?Z00EP5P0O2n2011000010121106000W?X~EP5P0O2n2011000010121106000W?XgEP5P0O2n2011000010121106000W?XfEP5P0O2n2011000010121106000W?XeEP5P0O2n2011000010121106000W?XdEP5P0O2n2011000010121106000W?XcEP5P0O2n2011000010121106000W?XbEP5P0O2n2011000010121106000W?XaEP5P0O2n2011000010121106000W?Z05EP5P0O2n2011000010121106000W?Z04EP5P0O2n2011000010121106000W?Z03EP5P0O2n2011000010121106000P~P{P|PMPZP[PLPJPcPWPVPdPeP^P_P`Q03PaQ0CPfQ0<P5MFzR5eWWWHQ02Q0EP5[]HeEybEbEbEbEbZbYPLPTE]WKWPWOWTW\W[WNWSW^WRWXWQWLWkXiEXm;WnWjWMX1EX2EX3EX4EXsEXrEX{EXzEXyEXxEXwEXvEXuEXtEX5EX6EX7EX8EX9EX:EX;EXJEXqEXpEX<EX=EX>EX}EXlEX|EWog033[eo"). Qed.
