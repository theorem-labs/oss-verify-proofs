(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZApiL ZHarnessL ZApiC ZHarnessC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ZApiInstC ZApiOkC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Open Scope Z_scope.

Definition the_zapiC : zapiC := ZApiInstC.zinstC.
Definition the_zapiC_ok : zapiC_ok the_zapiC := ZApiOkC.zinstC_ok.

Global Opaque the_zapiC.
