(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import MallocTree_u5 ASlot_I_u5 MallocFacts_AM_u5 MallocFacts_AMP_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Pm6 Require Import RMallocTree_u5 RMalloc_iface_u5 RAllocSlot_iface_u5 RF_malloc_core_u5 RF_malloc_top_u5 RASlot_I_u5 RF_alloc_slot_u5 RF_malloc_big_u5 RF_am_P_u5 RF_alloc_meta_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


Theorem rmalloc_spec : rmalloc_stmt.
Proof.
  exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

(* [comment removed for export] *)
Theorem rmalloc_spec_fit : rmalloc_stmt_fit.
Proof.
  exact (rmalloc_spec_fit_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.
End CEIL_WRAP_1.


