(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AsanNodesRP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition RP_HA : RPN.rptab := RPN.RPT 0x1c554c 0x1afb94 0x1afbec 0x5a6418 0x66ee38 0x5a6420 0x66fb28 0x5a6428 0x66fb30 0x5a6430 0x66fb20.
