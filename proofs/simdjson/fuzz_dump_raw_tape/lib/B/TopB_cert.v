(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images Require Import AsanUbsan.
From OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images Require Import Plain.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanTablesB AsanStartupB
  StartupHSBoth StartupPlanBoth BothStartupCert.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import RT_iface RT_iface2 RT_rep D_client TopA_iodefs RT_io TopA_start TopA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib Require Import TopLevelA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib Require Import ProofBase.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib Require Spec.ProgNoEnomem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GWf.
Lemma hs_ok_0 : hs_all_ok HS_both_0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_1000 : hs_all_ok HS_both_1000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_2000 : hs_all_ok HS_both_2000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_3000 : hs_all_ok HS_both_3000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma hs_if_some_ok : forall (P : acs -> Prop) (b : bool) (s : acs) (r : option acs) (ch : acs),
  P s -> (r = Some ch -> P ch) -> (if b then Some s else r) = Some ch -> P ch.
Proof. intros P b s r ch Ps Pr H. destruct b; [injection H as <-; exact Ps | exact (Pr H)]. Qed.

Lemma HS_both_ok : forall h ch, HS_both h = Some ch -> hs_all_ok ch = true.
Proof.
  intros h ch. unfold HS_both.
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_3000|].
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_2000|].
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_1000|].
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_0| discriminate].
Qed.

Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. reflexivity. Qed.

Section Client.

Variable CL : client_B.
Hypothesis HS_cl : forall h ch, HS_both h = Some ch -> cl_hs_ok CL ch = true.

Theorem s3s_B : rt_contracts2 RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) ->
  S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof using HS_cl.
  intros RC IOC.
  exact (s3s_A_of IT0 IT0_ok HS_both startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_both_ok CL HS_cl RC IOC).
Qed.

Theorem base_both_of : rt_contracts2 RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) -> impl_P_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof using HS_cl.
  intros RC IOC HP.
  exact (base_asan_of_cert IT0 IT0_ok HS_both startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_both_ok CL HS_cl
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
