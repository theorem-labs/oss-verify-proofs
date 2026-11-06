(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import StdioFiles BImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition exit_wr_ok (iv : Z * Z) : Prop :=
  ATOP <= fst iv \/ (RSTDERR <= fst iv /\ snd iv <= RSTDOUT + 232) \/ (0x6b1e78 <= fst iv /\ snd iv <= 0x6b1e80)
  \/ (0x6d1ef8 <= fst iv /\ snd iv <= 0x6d2120) \/ (0x179e10 <= fst iv /\ snd iv <= 0x179e11).
End CANSEC1.
