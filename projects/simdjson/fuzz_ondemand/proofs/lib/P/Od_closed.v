(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.MallocP Require Import RMalloc_iface RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Rnd Sj_iface Od_defs Od_arm_dbl_defs Od_arm_dbl_fhead Od_iter Od_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem od_iter_closed : od_iter_stmt.
Proof. intros E OK. exact (od_iterate_arms E OK (dbl_fhead E OK)). Qed.

Theorem rfuzz_one_closed : forall {CE__ : Ceiling} {RN__ : RunRnd}, rfuzz_one_stmt.
Proof. intros CE RN. exact (rfuzz_one_of_parts rmalloc_spec rfree_spec_proof od_iter_closed). Qed.
