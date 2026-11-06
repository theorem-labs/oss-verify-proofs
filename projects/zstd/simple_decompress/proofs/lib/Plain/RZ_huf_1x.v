(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import RZ_huf_iface RZ_huf_disp RZ_huf_dx1e RZ_huf_dx2e.

Theorem huf_1x_closed : huf_1x_stmt.
Proof. exact (huf_1x_proof huf_1x1_proof huf_1x2_proof). Qed.
