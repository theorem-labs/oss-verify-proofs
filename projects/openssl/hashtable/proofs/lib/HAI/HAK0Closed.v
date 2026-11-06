(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.hashtable.lib Require HAFullDefs HAK0Leaf HAK0MainA0 HAK0MainA2 HAK0MainA3 HAK0MainA1 HAK0MainB0 HAK0MainB2 HAK0MainB3 HAK0MainB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition k0_leaf_closed : HAFullDefs.file_leaf_stmt HAFullDefs.K0 HAFullDefs.T_file :=
  HAK0Leaf.k0_leaf HAK0MainA0.main25_a0 HAK0MainA2.main25_a2 HAK0MainA3.main25_a3 HAK0MainA1.main25_a1 HAK0MainB0.main25_b0 HAK0MainB2.main25_b2 HAK0MainB3.main25_b3 HAK0MainB1.main25_b1.
