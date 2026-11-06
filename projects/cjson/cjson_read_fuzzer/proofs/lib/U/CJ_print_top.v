(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require Bool.
From Stdlib Require List.
From Stdlib Require Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require NumFacts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require NumFactsG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require NumFacts_iface.
Module NumFactsG.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.NumFacts.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.

Theorem fmt_g_ret_proof : F_printf_iface.FMT_G_RET.
Proof. exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.NumFactsG.fmt_g_ret_proof. Qed.

Theorem fmt_g_len25_proof : F_printf_iface.FMT_G_LEN25.
Proof. exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.NumFactsG.fmt_g_len25_proof. Qed.

Theorem num_fmt_g_total_proof : NUM_FMT_G_TOTAL.
Proof. exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.NumFactsG.num_fmt_g_total_proof. Qed.

Theorem num_fmt_d_total_proof : NUM_FMT_D_TOTAL.
Proof. exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.NumFactsG.num_fmt_d_total_proof. Qed.

Theorem num_fmt_g_facts_proof : NUM_FMT_G_FACTS.
Proof. exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.NumFactsG.num_fmt_g_facts_proof. Qed.

Theorem num_sscanf_junk_proof : NUM_SSCANF_JUNK.
Proof. exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.NumFactsG.num_sscanf_junk_proof. Qed.
End NumFactsG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_iface CJ_print_iface CJ_pv_cases CJ_pv_objB CJ_pv_num.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_pv_objB.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_pv_objB.CJ_pvalue.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_pv_objB.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_pv_objB.CJ_print.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import NumFacts_iface.
Import NumFactsG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_printf_iface Scan_iface F_vsnprintf F_sscanf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Theorem pv_obj_case' : forall HI n, pv_case_at PV_OBJ_ENTRY HI n.
Proof. intros HI n. exact (pv_obj_case HI F_vsnprintf.sprintf_u04x_proof n). Qed.

Theorem pv_num_case' : forall HI n, pv_case_at PV_NUM_ENTRY HI n.
Proof.
  intros HI n.
  exact (pv_num_case HI F_vsnprintf.sprintf_d_proof F_vsnprintf.sprintf_g_proof F_sscanf.rsscanf_lg_proof
           fmt_g_ret_proof fmt_g_len25_proof num_fmt_g_facts_proof num_fmt_g_total_proof num_fmt_d_total_proof num_sscanf_junk_proof n).
Qed.

Theorem pvalue_spec' : forall HI n, pvalue_spec_at HI n.
Proof. intros HI n. exact (pvalue_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI) n). Qed.

Theorem print_spec' : forall HI, print_stmt HI.
Proof. intros HI. exact (print_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI)). Qed.

Theorem cjprint_spec' : forall HI, cjprint_stmt HI.
Proof. intros HI. exact (cjprint_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI)). Qed.

Theorem cjprintu_spec' : forall HI, cjprintu_stmt HI.
Proof. intros HI. exact (cjprintu_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI)). Qed.

Theorem pbuffered_spec' : forall HI, pbuffered_stmt HI.
Proof. intros HI. exact (pbuffered_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI)). Qed.


End CeilWrap.
