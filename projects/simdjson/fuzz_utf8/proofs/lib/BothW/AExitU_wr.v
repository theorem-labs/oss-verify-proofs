(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import StdioFiles BImg.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition exit_wr_ok (iv : Z * Z) : Prop :=
  ATOP <= fst iv \/ (RSTDERR <= fst iv /\ snd iv <= RSTDOUT + 232) \/ (0x6afad8 <= fst iv /\ snd iv <= 0x6afae0)
  \/ (0x6cfb58 <= fst iv /\ snd iv <= 0x6cfd80) \/ (0x177a10 <= fst iv /\ snd iv <= 0x177a11).
End CANSEC1.
