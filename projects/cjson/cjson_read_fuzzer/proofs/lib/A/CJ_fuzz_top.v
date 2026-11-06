(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface CJ_tree CJ_conv Scan_iface ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_fuzz_iface CJ_traces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_N2 CJ_parse_main CJ_pwlopts CJ_pwopts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz.CJ_delete.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pv_common CJ_pv_cases CJ_pv_top CJ_pv_ok CJ_pv_arr CJ_pv_obj CJ_ensure CJ_pstr_ok CJ_print CJ_printb CJ_fuzz ICPT_mem ICPT_mem2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_str3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_str3.ICPT_str.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_str3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_str3.ICPT_str2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_strtod.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Lemma flag_apart_of_flag_low : forall AI, art_flag_low_stmt AI -> flag_apart_stmt AI.
Proof. intros AI H. exact H. Qed.

(* [comment removed for export] *)
Theorem print_value_closed : forall AI TI, art_flag_low_stmt AI -> print_value_stmt AI TI.
Proof.
  intros AI TI FL.
  apply (print_value_ok AI TI FL).
  - exact (case_arr AI TI (ensure_ok AI TI) strlen_icpt_ok FL asan_memset_ok).
  - exact (case_obj AI TI (ensure_ok AI TI) strlen_icpt_ok FL asan_memset_ok (pstr_ok AI TI)).
Qed.

(* [comment removed for export] *)
Theorem pbuffered_closed : forall AI TI, art_flag_low_stmt AI -> pbuffered_stmt AI TI.
Proof. intros AI TI FL. exact (pbuffered_spec AI TI (print_value_closed AI TI FL) asan_memcpy_ok). Qed.

Theorem cjprint_closed : forall AI TI, art_flag_low_stmt AI -> cjprint_stmt AI TI.
Proof. intros AI TI FL. exact (cjprint_spec AI TI (print_value_closed AI TI FL) asan_memset_ok asan_memcpy_ok strlen_icpt_ok). Qed.

Theorem cjprintu_closed : forall AI TI, art_flag_low_stmt AI -> cjprintu_stmt AI TI.
Proof. intros AI TI FL. exact (cjprintu_spec AI TI (print_value_closed AI TI FL) asan_memset_ok asan_memcpy_ok strlen_icpt_ok). Qed.

(* [comment removed for export] *)
Theorem parse_value_closed : forall AI TI, art_flag_low_stmt AI -> sspw_stmt AI -> parse_value_stmt AI TI.
Proof.
  intros AI TI FL SSPW.
  exact (parse_value_spec AI TI (flag_apart_of_flag_low AI FL) (cjson_delete_spec AI TI) asan_memset_ok rstrtod_proof SSPW strncmp_icpt_ok).
Qed.

Theorem parse_wopts_closed : forall AI TI, art_flag_low_stmt AI -> sspw_stmt AI -> parse_wopts_stmt AI TI.
Proof.
  intros AI TI FL SSPW.
  exact (parse_wopts_spec AI TI strlen_icpt_ok
           (parse_wlopts_spec AI TI asan_memset_ok asan_memcpy_ok (cjson_delete_spec AI TI) (parse_value_closed AI TI FL SSPW))).
Qed.

(* [comment removed for export] *)
Theorem llvmfuzz_closed : forall AI TI, art_flag_low_stmt AI -> sspw_stmt AI -> llvmfuzz_stmt AI TI S_LIB.
Proof.
  intros AI TI FL SSPW.
  exact (llvmfuzz_spec AI TI (parse_wopts_closed AI TI FL SSPW) (pbuffered_closed AI TI FL) (cjprint_closed AI TI FL) (cjprintu_closed AI TI FL)).
Qed.


End CeilWrap.
