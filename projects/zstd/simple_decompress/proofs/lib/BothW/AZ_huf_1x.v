(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg AZ_huf_iface AZ_huf_dx1e AZ_huf_dx2e AZ_huf_disp.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Theorem huf_1x_closedA : huf_1x_stmtA.
Proof. exact (huf_1x_proofA huf_1x1_proofA huf_1x2_proofA). Qed.
End CANSEC1.
