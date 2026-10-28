(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AsanNodesRP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition RP_HA : RPN.rptab := RPN.RPT 0x1c04bc 0x1aab04 0x1aab5c 0x5dead8 0x6a1a78 0x5deae0 0x6a2768 0x5deae8 0x6a2770 0x5deaf0 0x6a2760.
