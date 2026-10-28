(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AZ_huf_iface AZ_huf_dx1e AZ_huf_dx2e AZ_huf_disp.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Theorem huf_1x_closedA : huf_1x_stmtA.
Proof. exact (huf_1x_proofA huf_1x1_proofA huf_1x2_proofA). Qed.
End CANSEC1.
