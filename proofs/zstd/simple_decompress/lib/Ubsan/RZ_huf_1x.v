(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_huf_iface RZ_huf_disp RZ_huf_dx1e RZ_huf_dx2e.

Theorem huf_1x_closed : huf_1x_stmt.
Proof. exact (huf_1x_proof huf_1x1_proof huf_1x2_proof). Qed.
