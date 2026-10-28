(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HTSpec HBFullDefs RowsHtBoth HBK0Closed HBKge1Closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition L0 : HBFullDefs.file_leaf_stmt HBFullDefs.K0 HBFullDefs.T_file := HBK0Closed.k0_leaf_closed.
Definition LK : HBFullDefs.file_leaf_stmt HBFullDefs.KGE1 HBFullDefs.T_file := HBKge1Closed.kge1_leaf_closed.

Definition base_closed := RowsHtBoth.strong_universal_error_free_hashtable_asan L0 LK.
