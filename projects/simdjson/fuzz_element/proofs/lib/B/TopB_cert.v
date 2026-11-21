(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the hand-off checks are evaluated on the hand-off states the start-up certificate computes for each CONFIG_RSEQ value instead of the recorded ones; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/B/TopB_cert.v, lines 12, 21-32, 37, 43, 52. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.simdjson.fuzz_element.images Require Import AsanUbsan.
From OSSVerify.simdjson.fuzz_element.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanTablesB AsanStartupB
  StartupPlanBoth BothStartupCert.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import RT_iface RT_iface2 RT_rep D_client TopA_iodefs RT_io TopA_start TopA.
From OSSVerify.Proofs.simdjson.fuzz_element.lib Require Import TopLevelA.
From OSSVerify.Proofs.simdjson.fuzz_element.lib Require Import ProofBase.
From OSSVerify.Proofs.simdjson.fuzz_element.lib Require Spec.ProgNoEnomem.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
(* ONE EVALUATION PER CLOSED [rseq_z b]: the hand-off states are the ones
   [AS/BothStartupCert.v] computes at that flag, and [hs_all_ok] reads the auxv's size
   [AUXSZ r = 432 + 32 * r].  [destruct b] leaves each branch closed for [vm_compute].
   Not a pin: both branches are discharged. *)
Lemma HS_both_ok : forall (b : bool) h ch, HS_both (rseq_z b) h = Some ch -> hs_all_ok (rseq_z b) ch = true.
Proof.
  intros b. apply (HS_both_forall (hs_all_ok (rseq_z b)) b).
  destruct b; vm_compute; reflexivity.
Qed.

Lemma startup_shape_holes : forall b : bool, holes_only (startup_shape (rseq_z b)) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Section Client.

Variable CL : client_B.
Hypothesis HS_cl : forall (b : bool) h ch, HS_both (rseq_z b) h = Some ch -> cl_hs_ok CL ch = true.

Theorem s3s_B : rt_contracts2 RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) ->
  S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof using HS_cl.
  intros RC IOC.
  exact (s3s_A_of IT0 IT0_ok HS_both startup_plan_r startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_both_ok CL HS_cl RC IOC).
Qed.

Theorem base_both_of : rt_contracts2 RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) -> impl_P_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof using HS_cl.
  intros RC IOC HP.
  exact (base_asan_of_cert IT0 IT0_ok HS_both startup_plan_r startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_both_ok CL HS_cl
           RC IOC HP Spec.ProgNoEnomem.prog_no_enomem_P).
Qed.

Theorem s3s_B_rc : rt_contracts2 RTA ->
  S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof using HS_cl. intros RC. exact (s3s_B RC rta_io). Qed.

Theorem base_both_rc : rt_contracts2 RTA -> impl_P_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof using HS_cl. intros RC HP. exact (base_both_of RC rta_io HP). Qed.
End Client.
