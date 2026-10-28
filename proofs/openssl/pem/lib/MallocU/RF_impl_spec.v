(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocTree ASlot_I MallocFacts_AM.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocTree RMalloc_iface RMalloc_impl RAllocSlot_iface RF_malloc_core RF_malloc_top RASlot_I RF_alloc_slot RF_malloc_big RF_am_P RF_alloc_meta RF_free_spec.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem rmalloc_impl_spec2 : rmalloc_impl_stmt2.
Proof.
  exact (rmalloc_impl_proof2 ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

Theorem rmalloc_impl_spec : rmalloc_impl_stmt.
Proof. exact (rmalloc_impl_of_2 rmalloc_impl_spec2). Qed.

Theorem rfree_impl_spec : rfree_impl_stmt.
Proof. exact rfree_impl_proof. Qed.
End WithCeiling0.
