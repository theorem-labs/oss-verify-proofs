(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_huf_iface RZ_huf_wksp RZ_huf_dx1e RZ_huf_4x1 RZ_huf_4x2.

Theorem huf_1x1_wksp_of_tbl : huf_rdx1_stmt -> huf_1x1_wksp_stmt.
Proof. intros HX1. exact (huf_1x1_wksp_proof HX1 huf_1x1_proof). Qed.

Theorem huf_4x_wksp_of_tbl : huf_rdx1_stmt -> huf_rdx2_stmt -> huf_4x_wksp_stmt.
Proof. intros HX1 HX2. exact (huf_4x_wksp_proof HX1 HX2 huf_4x1_closed huf_4x2_closed). Qed.
