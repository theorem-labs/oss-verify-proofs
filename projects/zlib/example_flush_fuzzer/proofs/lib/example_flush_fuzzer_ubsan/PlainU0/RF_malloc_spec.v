(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Malloc Require Import MallocTree ASlot_I MallocFacts_AM MallocFacts_AMP.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import RMallocTree RMalloc_iface RAllocSlot_iface RF_malloc_core RF_malloc_top RASlot_I RF_alloc_slot RF_malloc_big RF_am_P RF_alloc_meta.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Theorem rmalloc_spec : rmalloc_stmt.
Proof.
  exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

Theorem rmalloc_spec_z : rmalloc_stmt_z.
Proof.
  exact (rmalloc_spec_z_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.
Theorem rmalloc_spec_zz : rmalloc_stmt_zz.
Proof.
  exact (rmalloc_spec_zz_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

End CANSEC1.
