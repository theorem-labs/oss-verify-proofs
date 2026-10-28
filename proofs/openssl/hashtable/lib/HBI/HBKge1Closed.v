(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HBFullDefs HBKge1Leaf HBKFIA0 HBKFIA2 HBKFIA3 HBKFIA1 HBKFIB0 HBKFIB2 HBKFIB3 HBKFIB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition kge1_leaf_closed : HBFullDefs.file_leaf_stmt HBFullDefs.KGE1 HBFullDefs.T_file :=
  HBKge1Leaf.kge1_leaf_glue HBKFIA0.hfi_a0 HBKFIA2.hfi_a2 HBKFIA3.hfi_a3 HBKFIA1.hfi_a1 HBKFIB0.hfi_b0 HBKFIB2.hfi_b2 HBKFIB3.hfi_b3 HBKFIB1.hfi_b1.
