(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import StdioFiles AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition exit_wr_ok (iv : Z * Z) : Prop :=
  ATOP <= fst iv \/ (RSTDERR <= fst iv /\ snd iv <= RSTDOUT + 232) \/ (0x642e40 <= fst iv /\ snd iv <= 0x642e48)
  \/ (0x662ec0 <= fst iv /\ snd iv <= 0x6630e8) \/ (0x10c490 <= fst iv /\ snd iv <= 0x10c491).
End CANSEC1.
