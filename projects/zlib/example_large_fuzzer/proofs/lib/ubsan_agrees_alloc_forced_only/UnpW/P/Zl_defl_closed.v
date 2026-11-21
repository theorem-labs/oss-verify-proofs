(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZApi. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInst. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZApiL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInstL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MallocP Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Zlib_iface Zl_iface Drv_kit Z_zrd Z_trees_iface Z_defl_iface Zg_defl_iface Zl_defl_iface Z_trees_closed Zg_defl_closed Zl_slidehash Zl_dparams Zl_zrd Zl_deflate Zl_dparams_api Zl_dend Zl_dinit9.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem zlib_okL_defl_of : deflate_in_stmtg -> deflateParams_in_stmt ->
  rmalloc_stmt -> rfree_stmt -> RHEAP_blocks_nodup_stmt -> RHEAP_block_range_stmt -> RHEAP_blocks_disjoint_stmt -> RHEAP_frame_stmt ->
  tr_init_stmt ->
  forall R : zrepsL, zrd R = zr_dL ->
  deflateInit9_stmt R /\ deflate_stmtL R /\ deflateParams_stmt R /\ deflateEnd_stmtL R.
Proof.
  intros HDEFL HDP HMAL HFREE HND HBR HBD HFRAME HTRI R ER. split; [|split; [|split]].
  - exact (deflateInit9_proof HMAL HFREE HND HBR HBD HFRAME HTRI R ER).
  - exact (deflate_proofL HDEFL R ER).
  - exact (dparams_proofL HDP R ER).
  - exact (deflateEnd_proofL HFREE HND HBR HFRAME R ER).
Qed.

Theorem zlib_okL_defl : forall R : zrepsL, zrd R = zr_dL ->
  deflateInit9_stmt R /\ deflate_stmtL R /\ deflateParams_stmt R /\ deflateEnd_stmtL R.
Proof.
  exact (zlib_okL_defl_of deflate_in_g (deflateParams_spec deflate_in_g slide_hash_spec)
           rmalloc_spec rfree_spec_proof RHEAP_blocks_nodup_proof RHEAP_block_range_proof RHEAP_blocks_disjoint_proof RHEAP_frame_proof
           tr_init_closed).
Qed.
End WithCeiling0.
