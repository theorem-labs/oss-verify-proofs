(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.hashtable.lib Require HTSpec HAFullDefs RowsHtAsan RowsHtHalts HAK0Closed HAKge1Closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition L0 : HAFullDefs.file_leaf_stmt HAFullDefs.K0 HAFullDefs.T_file := HAK0Closed.k0_leaf_closed.
Definition LK : HAFullDefs.file_leaf_stmt HAFullDefs.KGE1 HAFullDefs.T_file := HAKge1Closed.kge1_leaf_closed.

Definition base_closed := RowsHtAsan.strong_universal_error_free_hashtable_asan L0 LK.
Definition halts_asan_closed := RowsHtHalts.halts_allowed_openssl_hashtable_halts_asan (RowsHtAsan.full16 L0 LK).
