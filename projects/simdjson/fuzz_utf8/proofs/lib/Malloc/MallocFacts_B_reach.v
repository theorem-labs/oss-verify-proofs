(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: copied from simdjson/fuzz_minifyimpl's proofs/lib/Malloc/MallocFacts_B_reach.v: module paths and target names for simdjson/fuzz_utf8. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Malloc Require Import MallocRep MallocTree MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


