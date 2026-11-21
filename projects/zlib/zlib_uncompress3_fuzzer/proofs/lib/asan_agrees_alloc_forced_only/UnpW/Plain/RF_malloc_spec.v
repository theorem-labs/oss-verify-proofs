(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Malloc Require Import MallocTree ASlot_I MallocFacts_AM MallocFacts_AMP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Plain Require Import RMallocTree RMalloc_iface RAllocSlot_iface RF_malloc_core RF_malloc_top RASlot_I RF_alloc_slot RF_malloc_big RF_am_P RF_alloc_meta.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Theorem rmalloc_spec : rmalloc_stmt.
Proof.
  exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

End CANSEC1.
