(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.openssl.pem.images Require Import Asan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import RT_iface RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin RT_freeFin RT_dsec HandoffLIB TopA TopA_cert.
From OssFuzzTheorems.Proofs.openssl.pem.lib Require Import ClaVerdict Spec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Top Require Import TopBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem rta_contracts_closed : rt_contracts RTA.
Proof.
  exact (rta_contracts (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
           (rta_free (drain_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok)).
Qed.

(* [comment removed for export] *)
Theorem A_realizes_of_client : forall C : cli_sigA, cli_okA C ->
  image_realizes Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs target_alloc_limit Spec.spec.
Proof. intros C HC. exact (A_realizes_of rta_contracts_closed C HC). Qed.
