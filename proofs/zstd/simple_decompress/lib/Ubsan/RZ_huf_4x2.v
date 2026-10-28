(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_iface2 RZ_huf_bitinit RZ_huf_fastargs RZ_huf_dx42_25.

Theorem huf_4x2_closed : huf_4x2_stmt.
Proof. exact (huf_4x2_proof bit_init_proof fast_args_proof2). Qed.
