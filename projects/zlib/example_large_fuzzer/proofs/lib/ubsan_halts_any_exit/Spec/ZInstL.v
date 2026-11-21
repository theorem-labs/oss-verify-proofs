(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZApiL ZHarnessL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require ZApiInstL ZApiOkL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Open Scope Z_scope.

Definition the_zapiL : zapiL := ZApiInstL.zinstL.
Definition the_zapiL_ok : zapiL_ok the_zapiL := ZApiOkL.zinstL_ok.
Global Opaque the_zapiL.
