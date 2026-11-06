(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel InitMem Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajlAlign UY_allocwrap UY_callbacks UY_buf_small UY_psmall UY_hex UY_buf UY_buf_append2 UY_lexalloc UY_yfree UY_yalloc UY_fuzz UY_decode.
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

(* [comment removed for export] *)
Lemma ywrap_malloc_closed : ywrap_malloc_stmt HK.        Proof. exact (ywrap_malloc_spec HK HKS RM). Qed.
Lemma ywrap_free_closed : ywrap_free_stmt HK.            Proof. exact (ywrap_free_spec HK HKS RF). Qed.
Lemma ywrap_realloc_closed : ywrap_realloc_stmt HK.      Proof. exact (ywrap_realloc_spec HK HKS RR). Qed.
Lemma ywrap_realloc_null_closed : ywrap_realloc_null_stmt HK. Proof. exact (ywrap_realloc_null_spec HK HKS RRN). Qed.

(* [comment removed for export] *)
Lemma ybuf_alloc_closed : ybuf_alloc_stmt HK.
Proof. exact (ybuf_alloc_spec HK HKS HKF HKB ywrap_malloc_closed). Qed.
Lemma ybuf_free_closed : ybuf_free_stmt HK.
Proof. exact (ybuf_free_spec HK HKS HKF HKB ywrap_free_closed). Qed.
Lemma ybuf_append_closed : ybuf_append_stmt HK.
Proof. exact (ybuf_append_spec HK HKS HKP HKF HKB ywrap_malloc_closed ywrap_realloc_closed). Qed.

(* [comment removed for export] *)
Lemma ylex_alloc_closed : ylex_alloc_stmt HK.
Proof. exact (ylex_alloc_spec HK HKS HKP HKF HKB ywrap_malloc_closed ybuf_alloc_closed). Qed.
Lemma ylex_free_closed : ylex_free_stmt HK.
Proof. exact (ylex_free_spec HK HKS HKP HKF HKB ywrap_free_closed ybuf_free_closed). Qed.

(* [comment removed for export] *)
Lemma yalloc_closed : yalloc_stmt HK.
Proof.
  exact (yalloc_spec HK HKS HKP HKF HKB ywrap_malloc_closed ywrap_realloc_null_closed
           yset_default_spec ybuf_alloc_closed ylex_alloc_closed).
Qed.
Lemma yfree_closed : yfree_stmt HK.
Proof. exact (yfree_spec HK HKS HKP HKF HKB ywrap_free_closed ybuf_free_closed ylex_free_closed). Qed.

(* [comment removed for export] *)
Lemma ystring_decode_closed : ystring_decode_stmt HK.
Proof. exact (ystring_decode_spec HK HKS HKF HKB ybuf_append_closed yhexToDigit_spec). Qed.

(* [comment removed for export] *)
Theorem yfuzz_closed : yparse_stmt HK -> yfuzz_stmt HK.
Proof. intros YPA. exact (yfuzz_spec HK HKS HKF HKB yalloc_closed YPA yfree_closed). Qed.
End S.
End RC__1.
