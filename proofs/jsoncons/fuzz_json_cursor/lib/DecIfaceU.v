(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import DecIface.
Open Scope Z_scope.

Module PDCU.
(* The decimal-float, scanexp, guard-cell, thread-pointer and image addresses of the second image. *)
Definition ubsan11 : PDC.addrs := PDC.ADDRS 0xb2a80 0xb2bd0 0xb458c 0xf6a70 0xd6800 0x10000 0xc3a78.
End PDCU.
