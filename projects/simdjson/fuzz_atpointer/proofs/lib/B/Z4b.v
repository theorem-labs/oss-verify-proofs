(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvw Z4d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt Zi4 RT_rtf D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3
  Sj_new Zpt Zps Zpo Zq0 Zvr Zwn Zsl Z4a Z73 Z5g Z6m Z3q Z3p
  Z43 Z42 Z6l Z71 Z5h Z5i Z5j Z6q Z6y Z6r Z6s Z6t Z6x Z6v Z6p
  Z45 Z4e Z4c Z4l Z4m Z4n Z4o Z52 Z57 Z54 Z56 Z55
  Z5k Z5b Z4q Z59 Z5a Z5c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section ClosedA.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC2 : rt_contracts2 RT.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.
Hypothesis AFI : forall Σ m, ART RT Σ m -> vt_impl m.
Hypothesis S2 : stage2at_cps RT.

Hypothesis SPL : splitinto_cpsA RT.
Hypothesis EMPF : emplf_cpsA RT.
Hypothesis EMPS : empls_cpsA RT.
Hypothesis VDES : vdestroy_cpsA RT.
Hypothesis HELEM : forall E, aenvA_ok E -> atp_elem_cpsA RT E TAPE_MAX_DEPTH.

Let RTF : rt_contracts_f RT := rtf_of_rt RT (rc2_rt RT RC2).
Let NEW1 := new_nt_ok RT AF (rf_malloc RT RTF).
Let NEWA := newarr_nt_ok RT AF (rf_malloc RT RTF).
Let DELA := delarr_ok RT AF (rf_free RT RTF).
Let DEL1 := del_ok RT AF (rf_free RT RTF).
Let MSET := rf_asan_memset RT RTF.
Let MCPY := rf_asan_memcpy RT RTF.

Theorem parse_closedA : parse_cps RT.
Proof using AF RC2 S2. exact (parse_ok RT AF (stage1_ok RT AF MCPY) S2). Qed.

Theorem parse0_closedA : parse0_cps RT.
Proof using AF RC2. exact (parse0_ok RT AF (stage1z_ok RT AF MCPY)). Qed.

Theorem create_closedA : create_cps RT.
Proof using AF RC2 AFC AFV. exact (create_ok RT AF NEW1 MSET (setcap_ok RT AF NEWA AFC) (setmd_ok RT AF NEWA AFC) AFC AFV). Qed.

Theorem pid_closedA : pid_cps RT sj_lib.
Proof using AF RC2 AFC AFV AFI S2. exact (pid_ok RT AF RTF parse_closedA (allocate_ok RT AF NEWA AFC) create_closedA AFV AFI). Qed.

Theorem pid0_closedA : pid0_cps RT sj_lib.
Proof using AF RC2 AFC AFV AFI. exact (pid0_ok RT AF RTF parse0_closedA (allocate_ok RT AF NEWA AFC) create_closedA AFV AFI). Qed.

Theorem pdtor_closedA : pdtor_cps RT (pdone RT).
Proof using AF RC2 AFV. exact (pdtor_ok RT AF (docdtor_ok RT AF DELA) (deldtor_ok RT AF DELA DEL1) AFV). Qed.

Theorem fuzz_one_closedA : fuzz_one_cps RT sj_lib.
Proof using AF RC2 AFC AFV AFI S2 SPL EMPF EMPS VDES HELEM.
  exact (fuzz_one_t2A RT sj_lib sj_lib_loc AF (rc2_rt RT RC2) (rf_stack_malloc_2 RT RTF) MSET MCPY NEWA DELA AFC SPL EMPF EMPS VDES pid_closedA pid0_closedA pdtor_closedA HELEM).
Qed.

End ClosedA.
