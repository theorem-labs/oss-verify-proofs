(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_bitinit RZ_huf_fastargs RZ_huf_dx41w.

Theorem huf_4x1_closed : huf_4x1_stmt.
Proof. exact (huf_4x1_proof bit_init_proof fast_args_proof). Qed.
