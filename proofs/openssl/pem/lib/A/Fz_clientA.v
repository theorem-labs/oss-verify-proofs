(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.openssl.pem.images Require Import Asan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import A_Chain.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import RT_iface RT_iface_pem RT_state RT_rep RT_census RT_gshacc RT_artfacts RT_iclifts_pem RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_contracts_pem RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin RT_freeFin RT_dsec RT_tsd RT_gap I_strncmp0 D_libiface D_libiface_pem Fz_ckit HandoffLIB TopA TopA_cert TopA_final Fz_lib0 Fz_lib0test Fz_libA Fz_I3_top Fz_initA Fz_initA_go Fz_callA Fz_goA_call.
From OssFuzzTheorems.Proofs.openssl.pem.lib Require Import ClaVerdict Spec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Top Require Import TopBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Theorem rta_contracts_pem_closed : rt_contracts_pem RTA.
Proof.
  exact (rta_contracts_pem (refill_ok fixed_commit_ok) (drain_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok).
Qed.

Theorem cli_rt_RTA : cli_rt RTA B_GOBJ.
Proof. exact (mkCliRT RTA B_GOBJ rta_art_facts rta_art_facts_pem_B rta_contracts_closed rta_contracts_pem_closed). Qed.

(* [comment removed for export] *)
Lemma cg_sub_init : cg_sub FI_SITES FI_CALLS CENSUS_SITES CENSUS_CALLS.
Proof. apply cg_sub_lit; vm_compute; reflexivity. Qed.
Lemma cg_sub_call : cg_sub CALLA_SITES CALLA_CALLS CENSUS_SITES CENSUS_CALLS.
Proof. apply cg_sub_lit; vm_compute; reflexivity. Qed.

Definition C_A : cli_sigA := mkCliA LIB0_A LIB_A CENSUS_SITES CENSUS_CALLS TEST_A.

Theorem clientA_ok : cli_okA C_A.
Proof.
  unfold cli_okA, C_A; cbn [ca_lib0 ca_lib ca_sites ca_calls ca_test].
  split; [exact lib0_at_main_A|]. split; [exact test_A_2|]. split; [exact test_A_3|]. split; [exact lib0_local_A|]. split; [exact lib_local_A|].
  split; [exact (fuzz_init_closed RTA B_GOBJ cli_rt_RTA rta_tsd rta_errno_acc (gobj_lift_exact _ (proj1 initA_go)) (gobj_lift_cover _ (proj2 initA_go)) CENSUS_SITES CENSUS_CALLS cg_sub_init)|].
  split; [exact (W7_one_A RTA B_GOBJ cli_rt_RTA rta_strncmp0 rta_tsd rta_errno_acc go_call_A CENSUS_SITES CENSUS_CALLS cg_sub_call)|].
  split; apply incl_refl.
Qed.

(* [comment removed for export] *)
Theorem A_realizes :
  image_realizes Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs target_alloc_limit Spec.spec.
Proof. exact (A_realizes_of_client C_A clientA_ok). Qed.
