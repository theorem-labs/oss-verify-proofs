(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim ZApi ZHarness.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require ZApiInst ZApiOk.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition the_zapi : zapi := ZApiInst.zinst.
Definition the_zapi_ok : zapi_ok the_zapi := ZApiOk.zinst_ok.
Global Opaque the_zapi.
