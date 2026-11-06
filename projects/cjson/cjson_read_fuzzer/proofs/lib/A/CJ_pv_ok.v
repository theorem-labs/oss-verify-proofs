(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface CJ_conv CJ_traces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_iface ICPT_fmt_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface.NumFacts_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_numB1 CJ_pv_top.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_ensure CJ_pstr_ok ICPT_mem ICPT_mem2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_sprintf_b.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_sprintf_b.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_sscanf_b.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_sscanf_b NumFactsG CJ_fmt_glue.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Theorem print_value_ok : forall (AI : art_iface) (TI : trs_iface),
  art_flag_low_stmt AI -> CASEH AI TI PV_ARR_ENTRY -> CASEH AI TI PV_OBJ_ENTRY -> print_value_stmt AI TI.
Proof.
  intros AI TI FL ARR OBJ.
  exact (print_value_spec AI TI (CJ_ensure.ensure_ok AI TI) (CJ_pstr_ok.pstr_ok AI TI) FL ICPT_mem.asan_memset_ok ICPT_mem2.asan_memcpy_ok
           (CJ_fmt_glue.art_fmt_facts AI) (CJ_fmt_glue.art_fmt_lits AI)
           ICPT_sprintf_b.asprintf_d_ok_b (ICPT_sprintf_b.asprintf_g_ok_b 15) (ICPT_sprintf_b.asprintf_g_ok_b 17) ICPT_sscanf_b.asscanf_lg_ok_b
           NumFactsG.fmt_g_ret_proof NumFactsG.fmt_g_len25_proof NumFactsG.num_fmt_g_facts_proof NumFactsG.num_fmt_g_total_proof
           NumFactsG.num_fmt_d_total_proof NumFactsG.num_sscanf_junk_proof ARR OBJ).
Qed.


End CeilWrap.
