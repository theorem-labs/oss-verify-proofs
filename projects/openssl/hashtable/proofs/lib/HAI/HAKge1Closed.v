(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.hashtable.lib Require HAFullDefs HAKge1Leaf HAKFIA0 HAKFIA2 HAKFIA3 HAKFIA1 HAKFIB0 HAKFIB2 HAKFIB3 HAKFIB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition kge1_leaf_closed : HAFullDefs.file_leaf_stmt HAFullDefs.KGE1 HAFullDefs.T_file :=
  HAKge1Leaf.kge1_leaf_glue HAKFIA0.hfi_a0 HAKFIA2.hfi_a2 HAKFIA3.hfi_a3 HAKFIA1.hfi_a1 HAKFIB0.hfi_b0 HAKFIB2.hfi_b2 HAKFIB3.hfi_b3 HAKFIB1.hfi_b1.
