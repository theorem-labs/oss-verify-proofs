(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From stdpp Require Import bitvector.definitions.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[global] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
(* [comment removed for export] *)
Definition bvkh_test : bv 64 := 0x4b928%bv.
