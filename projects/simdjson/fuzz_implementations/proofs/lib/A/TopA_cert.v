(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the hand-off checks are evaluated on the hand-off states the start-up certificate computes for each CONFIG_RSEQ value instead of the recorded ones; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/A/TopA_cert.v, lines 12, 21-32. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Asan.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanTablesA AsanStartup
  StartupPlanAsan AsanStartupCert.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import RT_iface RT_iface2 RT_rep D_defs I_iodefs X_xdefs Imp_libifaceA Imp_handoffA TopA_iodefs RT_io TopA_start TopA.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Import TopLevelA.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Import ProofBase.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Spec.ProgNoEnomem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.
(* ONE EVALUATION PER CLOSED [rseq_z b]: the hand-off states are the ones
   [AS/AsanStartupCert.v] computes at that flag, and [hs_all_ok] reads the auxv's size
   [AUXSZ r = 432 + 32 * r].  [destruct b] leaves each branch closed for [vm_compute].
   Not a pin: both branches are discharged. *)
Lemma HS_asan_ok : forall (b : bool) h ch, HS_asan (rseq_z b) h = Some ch -> hs_all_ok (rseq_z b) ch = true.
Proof.
  intros b. apply (HS_asan_forall (hs_all_ok (rseq_z b)) b).
  destruct b; vm_compute; reflexivity.
Qed.

Lemma startup_shape_holes : forall b : bool, holes_only (startup_shape (rseq_z b)) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Section Main.

Hypothesis MAIN : forall argv fs, valid_argv argv -> forall c, START RTA OUT_repA ERR_repA XENVA (imp_libA None) argv fs c -> realizes asegs c (canonT (argv_Z argv) fs).

Theorem s3s_A : S3s_stmt_e Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof using MAIN.
  exact (s3s_A_of IT0 IT0_ok HS_asan startup_plan_r startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_asan_ok HS_imp_ok MAIN).
Qed.

Theorem base_asan_of : impl_P_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof using MAIN.
  intros HP.
  exact (base_asan_of_cert IT0 IT0_ok HS_asan startup_plan_r startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_asan_ok HS_imp_ok MAIN
           HP Spec.ProgNoEnomem.prog_no_enomem_P).
Qed.
End Main.
