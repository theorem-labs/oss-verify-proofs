(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UbsanClosed PC_client.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2U Require Import PU2_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem ubsan_client_closed : ubsan_client_stmt.
Proof. exact (ubsan_client_mod_stage2 stage2_closed). Qed.
