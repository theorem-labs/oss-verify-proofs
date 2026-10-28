(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX RMalloc_iface Harness_iface RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RF_fse_iface RF_fse_iface_m RF_fse_leaf RF_fse_prod RF_fse_write_C.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RF_fse_h_malloc RF_fse_h.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Theorem fuzz_one_closed : fse_read_stmt -> fuzz_one_stmt.
Proof.
intros READ.
exact (fuzz_one_proof
(prod_create_proof (fuzz_malloc_proof rmalloc_spec))
(fuzz_malloc_proof rmalloc_spec)
rfree_spec_proof
(prod_free_proof rfree_spec_proof)
prod_u32r_proof (prod_i32r_proof prod_u32r_proof)
fse_wbound_proof fse_write_proof fse_iserror_proof READ).
Qed.
End CANSEC1.
