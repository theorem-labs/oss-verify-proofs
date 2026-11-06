(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsB Od_cpsB Od_loopB Od_hkit0A Od_deldtorA Od_beginB Od_topB
  Od_headB Od_plusB Od_arm_rawB Od_arm_contB Od_arm_litB Od_arm_nullB Od_arm_intB Od_arm_strB Od_arm_nestB Od_pstr_defsB Od_pstrB Od_fromchB
  Od_arm_dbl_exitB Od_arm_dblcB Od_exitpB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Closed.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis DELA : del_cps RT e_delarr.
Hypothesis DTOR : deldtor_cps RT.
Hypothesis VDES : vdestroy_cpsA RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.
Hypothesis AFG : forall Σ m, ART RT Σ m -> ro_cells bsegs m OD_GOT_TABS od_got_cells.
Hypothesis HFROMCH : forall PMc, fdfs_only PMc -> mat_stable PMc -> fromchb_stmt RT PMc.
Hypothesis DBLE : forall E, od_oka E -> od_shb E -> arm_dbl_evt E.
Hypothesis SETUP : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_setup_stmt RT LIB PMc.

Lemma HEADc : forall E, od_oka E -> od_shb E -> HLASTP E -> od_head_stmt E.
Proof using.
  intros E OK HG HL.
  exact (od_head E OK HL (od_arm_string E OK pstrb_spec HG) (od_arm_bool E OK) (od_arm_array E OK) (od_arm_int64 E OK)
           (od_arm_object E OK) (od_arm_uint64 E OK) (od_arm_raw E OK) (od_arm_null E OK) (od_arm_begin E OK) (od_arm_nest E OK HG)).
Qed.
Lemma HEXITc : forall E, od_oka E -> od_head_exit_stmt E.
Proof using. exact od_head_exit. Qed.
Lemma PLUSc : forall E, od_oka E -> od_shb E -> HLASTP E -> od_plus_stmt E.
Proof using. exact od_plus_top. Qed.
Lemma BEGINc : forall E, od_oka E -> od_shb E -> od_begin_stmt E.
Proof using. exact od_iterate. Qed.
Lemma DBLc : forall PMc, fdfs_only PMc -> mat_stable PMc -> arm_dbl_cps RT PMc.
Proof using AF AFV AFG HFROMCH DBLE.
  intros PMc FDO MST.
  exact (od_arm_dbl_cps RT AF PMc MST AFV AFG (HFROMCH PMc FDO MST) DBLE (fun E OK _ => dbl_resume E OK)).
Qed.
Lemma EXITPc : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_exitp_stmt RT LIB PMc.
Proof using LIB_loc AF RTF DELA DTOR VDES AFV.
  intros PMc FDO MST. exact (od_exit RT LIB LIB_loc AF PMc FDO MST RTF DELA DTOR VDES AFV).
Qed.

Theorem fuzz_one_closed_odB : fuzz_one_cps RT LIB.
Proof using AF LIB_loc RTF DELA DTOR VDES AFV AFG HFROMCH DBLE SETUP.
  apply (fuzz_one_odB RT LIB AF HEADc HEXITc PLUSc BEGINc DBLc); [| exact EXITPc].
  intros PMc Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo FDO MST.
  exact (SETUP PMc FDO MST Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo FDO MST).
Qed.

End Closed.
