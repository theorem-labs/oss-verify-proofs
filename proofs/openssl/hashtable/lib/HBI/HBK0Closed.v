(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HBFullDefs HBK0Leaf HBK0MainA0 HBK0MainA2 HBK0MainA3 HBK0MainA1 HBK0MainB0 HBK0MainB2 HBK0MainB3 HBK0MainB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition k0_leaf_closed : HBFullDefs.file_leaf_stmt HBFullDefs.K0 HBFullDefs.T_file :=
  HBK0Leaf.k0_leaf HBK0MainA0.main25_a0 HBK0MainA2.main25_a2 HBK0MainA3.main25_a3 HBK0MainA1.main25_a1 HBK0MainB0.main25_b0 HBK0MainB2.main25_b2 HBK0MainB3.main25_b3 HBK0MainB1.main25_b1.
