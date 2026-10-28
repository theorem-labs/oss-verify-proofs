(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_bitinit RZ_huf_fastargs RZ_huf_dx41w.

Theorem huf_4x1_closed : huf_4x1_stmt.
Proof. exact (huf_4x1_proof bit_init_proof fast_args_proof2). Qed.
