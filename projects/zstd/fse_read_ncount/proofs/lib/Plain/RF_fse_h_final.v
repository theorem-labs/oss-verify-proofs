(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg Harness_iface RF_fse_iface RF_fse_h_asm RF_fse_rd.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import RunDraw.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Theorem fuzz_one_final : fuzz_one_stmt.
Proof. exact (fuzz_one_closed fse_read_proof). Qed.
End CANSEC1.
