(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocTree ASlot_I MallocFacts_AM MallocFacts_AMP.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocTree HP_RMalloc_iface HP_RAllocSlot_iface HP_RF_malloc_core HP_RF_malloc_top HP_RASlot_I HP_RF_alloc_slot HP_RF_malloc_big HP_RF_am_P HP_RF_alloc_meta.

Section RP_1. Context {hRP : run_params}.
#[using="Type"] Theorem rmalloc_spec : rmalloc_stmt.
Proof.
  exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro
           (fun st0 st st1 sc idx g b AI I0 => ai_under st0 st st1 sc idx AI I0 g b)
           (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.


End RP_1.
