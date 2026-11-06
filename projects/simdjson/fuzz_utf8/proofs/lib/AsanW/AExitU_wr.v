(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import StdioFiles AImg.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition exit_wr_ok (iv : Z * Z) : Prop :=
  ATOP <= fst iv \/ (RSTDERR <= fst iv /\ snd iv <= RSTDOUT + 232) \/ (0x6a3758 <= fst iv /\ snd iv <= 0x6a3760)
  \/ (0x6c37d8 <= fst iv /\ snd iv <= 0x6c3a00) \/ (0x16b690 <= fst iv /\ snd iv <= 0x16b691).
End CANSEC1.
