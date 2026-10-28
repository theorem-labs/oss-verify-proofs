(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin RT_freeFin RT_dsec RT_calloc RT_refreeG RT_redrain_ldefs RT_redrain_istmt RT_redrain_fin RT_redsec RT_realloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem rta_refill_closed : refill_stmt.
Proof. exact (refill_ok fixed_commit_ok). Qed.

Theorem rta_core_sec_closed : core_stmt_sec.
Proof. exact (mal_core_sec grant_node_ok fixed_commit_pab_ok). Qed.

Theorem rta_free_closed : free_contract RTA.
Proof. exact (rta_free (drain_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok). Qed.

Theorem rta_malloc_closed : malloc_contract RTA.
Proof. exact (RT_malloc.rta_malloc (RT_malcore_m.core_prim rta_refill_closed) rta_core_sec_closed). Qed.

Theorem rta_calloc_closed : calloc_contract RTA.
Proof. exact (RT_calloc.rta_calloc rta_refill_closed). Qed.

(* [comment removed for export] *)
Theorem rta_contracts_closed : realloc_contract RTA -> rt_contracts RTA.
Proof. exact (rta_contracts rta_refill_closed rta_core_sec_closed rta_free_closed). Qed.

(* [comment removed for export] *)
Theorem rta_drain_r_closed : drain_stmt_r.
Proof. exact (drain_ok_r fixed_commit_ok (fun p HOK => item_sec_ok_r p munmap_ok madvise_ok HOK)). Qed.

Theorem rta_realloc_closed : realloc_contract RTA.
Proof. exact (RT_realloc.rta_realloc rta_refill_closed rta_drain_r_closed fixed_commit_ok). Qed.

Theorem rta_contracts_all : rt_contracts RTA.
Proof. exact (rta_contracts_closed rta_realloc_closed). Qed.

(* [comment removed for export] *)
Lemma rta_live_pos : forall (Σ : rts RTA) m p n, ART RTA Σ m -> In (p, n) (rt_live RTA Σ) -> (0 < n)%Z.
Proof.
  intros Σ m p n HA Hin. cbn [ART rt_live RTA] in HA, Hin. unfold rtA_live in Hin.
  pose proof (ART_wf Σ m HA) as (_ & RW & (_ & _ & V3 & _) & SW & _).
  destruct (V3 p n Hin) as [(c & i & Hc & Hn & _)|(s & Hs & _ & Hsn & _)].
  - destruct RW as (R1 & _). pose proof (R1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FA & _).
    pose proof (proj1 (Forall_forall _ _) FA _ (nth_error_In _ _ Hn)) as X. cbn beta iota in X. lia.
  - destruct SW as (_ & _ & _ & SW4 & _). pose proof (proj1 (Forall_forall _ _) SW4 s Hs) as ((T1 & _) & _). lia.
Qed.

