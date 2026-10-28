(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_huf_iface RZ_huf_disp RZ_huf_4x1 RZ_huf_4x2.

Theorem huf_4x_closed : huf_4x_stmt.
Proof. exact (huf_4x_proof huf_4x1_closed huf_4x2_closed). Qed.
