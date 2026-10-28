(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import Plain.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import RT_iface RT_iface2 RT_state RT_rep RT_stackmalloc RT_stackmalloc1 RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_contracts2 RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin RT_freeFin RT_dsec RT_drain_rhead RT_freeP RT_io TopA_iodefs D_defs I_iodefs X_xdefs Imp_libifaceA TopA_cert RT_smgc.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan StartupHSBoth.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib Require Import ProofBase TopLevelA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.
Definition rta_rc2_closed : rt_contracts2 RTA :=
  rta_contracts2 (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
    (rta_free (drain_ok rhead_empty_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok (free_pass_ok munmap_ok madvise_ok)) smgc_proof smgc1_proof.

Section Final.
Hypothesis MAINR : rt_contracts2 RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) ->
  forall argvb fs, valid_argv argvb -> forall c, START RTA OUT_repA ERR_repA XENVA (imp_libA None) argvb fs c -> realizes bsegs c (canonT (argv_Z argvb) fs).

Theorem base_asan : impl_P_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof using MAINR. intros HP. exact (base_asan_of (MAINR rta_rc2_closed rta_io) HP). Qed.

Theorem s3s_asan : S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof using MAINR. exact (s3s_A (MAINR rta_rc2_closed rta_io)). Qed.
End Final.
