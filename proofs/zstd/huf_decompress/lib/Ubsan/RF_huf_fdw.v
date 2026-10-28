(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT
  HufPure_FseReadBridge.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit StrFun WStr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_iface2 RF_huf_tbl_kit
  RF_huf_bdt_model RF_huf_fdw_cut RF_huf_fdw_si RF_huf_fdw_fi RF_huf_fdw_top RF_huf_rnc RF_huf_bdt RF_huf_initds
  RF_huf_fdw_sm RF_huf_fdw_st RF_huf_fdw_stc RF_huf_fdw_fm RF_huf_fdw_ft.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem fse_decomp_of_parts : fse_build_stmt -> fse_init_dstate_stmt ->
  fdw_l1_stmt -> fdw_t1_stmt -> fdw_l3_stmt -> fdw_t2_stmt -> fse_decomp_stmt.
Proof.
  intros BUILD INIT L1 T1 L3 T2.
  exact (fdw_top fse_readh_proof BUILD (fdw_nf_entry_proof INIT L1 T1) (fdw_f_entry_proof INIT L3 T2)).
Qed.

Theorem fse_decomp_of_l1 : fdw_l1_stmt -> fse_decomp_stmt.
Proof.
  intros L1.
  exact (fse_decomp_of_parts fse_build_proof fse_init_dstate_proof L1 fdw_t1_proof fdw_l3_proof
           (fdw_t2_proof fdw_fin1_proof fdw_fin2_proof)).
Qed.

Lemma fse_decomp_proof : fse_decomp_stmt.
Proof. exact (fse_decomp_of_l1 fdw_l1_proof). Qed.
(* [comment removed for export] *)
