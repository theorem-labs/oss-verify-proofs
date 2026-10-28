(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.simdjson.fuzz_dump.images Require Import AsanUbsan.
From OssFuzzTheorems.simdjson.fuzz_dump.images Require Import Plain.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import RT_iface RT_iface2 RT_state RT_rep RT_stackmalloc RT_stackmalloc1 RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_contracts2 RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin RT_freeFin RT_dsec RT_drain_rhead RT_freeP D_client TopB_cert RT_smgc.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan StartupHSBoth.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib Require Import ProofBase TopLevelA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GWf.
Theorem base_both : forall CL : client_B,
  (forall h ch, HS_both h = Some ch -> cl_hs_ok CL ch = true) ->
  impl_P_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  intros CL HS_cl HP.
  exact (base_both_rc CL HS_cl
           (rta_contracts2 (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
              (rta_free (drain_ok rhead_empty_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok (free_pass_ok munmap_ok madvise_ok)) smgc_proof smgc1_proof) HP).
Qed.

Theorem s3s_both : forall CL : client_B,
  (forall h ch, HS_both h = Some ch -> cl_hs_ok CL ch = true) ->
  S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  intros CL HS_cl.
  exact (s3s_B_rc CL HS_cl
           (rta_contracts2 (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
              (rta_free (drain_ok rhead_empty_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok (free_pass_ok munmap_ok madvise_ok)) smgc_proof smgc1_proof)).
Qed.
