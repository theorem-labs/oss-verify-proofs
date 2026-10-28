(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX Harness_iface RF_fse_iface RF_fse_h_asm RF_fse_rd.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Theorem fuzz_one_final : fuzz_one_stmt.
Proof. exact (fuzz_one_closed fse_read_proof). Qed.
End CANSEC1.
