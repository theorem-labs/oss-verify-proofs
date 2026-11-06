(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_callbacks UY_buf_small UY_psmall UY_allocwrap UYajl_asm UY_parse_val UY_parse_val2 UY_parse_esc UY_parse_loop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis RM : rmalloc_rz_stmt HK.
Hypothesis RF : rfree_rz_stmt HK.
Hypothesis RR : rrealloc_rz_stmt HK.
Hypothesis RRN : rrealloc_null_rz_stmt HK.
Hypothesis YLX : ylex_lex_stmt HK.

Let YWR : ywrap_realloc_stmt HK := ywrap_realloc_closed HK HKS RR.
Let YRP : yreset_parser_stmt := yreset_parser_spec (ylex_realloc_spec ybuf_clear_spec).
Let YSD : ystring_decode_stmt HK := ystring_decode_closed HK HKS HKP HKF HKB RM RR.
Let VSE : val_esc_stmt HK := val_esc_proof HK HKS HKP HKF HKB YSD ybuf_clear_spec ybuf_err_spec ybuf_data_spec ybuf_len_spec ycb_string_spec YWR YRP.
Let PV : pass_val_stmt HK := pass_val HK HKS HKP HKF HKB YLX YWR YRP ycb_null_spec ycb_boolean_spec ycb_number_spec ycb_string_spec
           ycb_start_map_spec ycb_start_array_spec ycb_end_array_spec VSE.

Theorem ydo_parse_closed : ydo_parse_stmt HK.
Proof.
  exact (ydo_parse_spec HK HKS HKP HKF HKB YLX ycb_end_array_spec ycb_end_map_spec ycb_map_key_spec YSD
           ybuf_clear_spec ybuf_err_spec ybuf_data_spec ybuf_len_spec ybs_set_spec PV).
Qed.

Theorem yparse_closed : yparse_stmt HK.
Proof.
  exact (yparse_spec HK HKS HKP HKF HKB YLX ycb_end_array_spec ycb_end_map_spec ycb_map_key_spec YSD
           ybuf_clear_spec ybuf_err_spec ybuf_data_spec ybuf_len_spec ybs_set_spec PV).
Qed.

(* [comment removed for export] *)
Theorem yfuzz_closed_lex : yfuzz_stmt HK.
Proof. exact (yfuzz_closed HK HKS HKP HKF HKB RM RF RRN yparse_closed). Qed.
End S.
End RC__1.
