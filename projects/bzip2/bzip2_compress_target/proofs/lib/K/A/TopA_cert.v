(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require AxSymExec3 AsanPlanCore AsanPlan AsanTablesB AsanStartupB StartupHSBoth StartupPlanBoth BothStartupCert.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require RT_iface RT_rep D_libiface L_libA TopA_iodefs RT_io TopA_start TopA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require TopLevelA.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanTablesB AsanStartupB
  StartupHSBoth StartupPlanBoth BothStartupCert.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_iodefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_io.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_start.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require Import TopLevelA.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma hs_ok_0 : hs_all_ok HS_both_0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_1000 : hs_all_ok HS_both_1000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_2000 : hs_all_ok HS_both_2000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_3000 : hs_all_ok HS_both_3000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma hs_if_some_ok : forall (P : acs -> Prop) (b : bool) (s : acs) (r : option acs) (ch : acs),
  P s -> (r = Some ch -> P ch) -> (if b then Some s else r) = Some ch -> P ch.
Proof. intros P b s r ch Ps Pr H. destruct b; [injection H as <-; exact Ps | exact (Pr H)]. Qed.

Lemma HS_asan_ok : forall h ch, HS_both h = Some ch -> hs_all_ok ch = true.
Proof.
  intros h ch. unfold HS_both.
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_3000|].
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_2000|].
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_1000|].
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_0| discriminate].
Qed.

(* [comment removed for export] *)
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem s3s_A : rt_contracts RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) -> fuzz_one_cps RTA LIB_A ->
  S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  intros RC IOC FUZZ.
  exact (s3s_A_of IT0 IT0_ok HS_both startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_asan_ok RC IOC FUZZ).
Qed.

(* [comment removed for export] *)
Theorem s3s_A_rc : rt_contracts RTA -> fuzz_one_cps RTA LIB_A ->
  S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof. intros RC FUZZ. exact (s3s_A RC rta_io FUZZ). Qed.

(* [comment removed for export] *)
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Asan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanTablesA AsanStartup
  StartupHSAsan StartupPlanAsan AsanStartupCert.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import RT_iface RT_rep D_libiface L_libA TopA_iodefs RT_io TopA_start TopA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require Import TopLevelA.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma hs_ok_0 : hs_all_ok HS_asan_0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_1000 : hs_all_ok HS_asan_1000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_2000 : hs_all_ok HS_asan_2000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_3000 : hs_all_ok HS_asan_3000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma hs_if_some_ok : forall (P : acs -> Prop) (b : bool) (s : acs) (r : option acs) (ch : acs),
  P s -> (r = Some ch -> P ch) -> (if b then Some s else r) = Some ch -> P ch.
Proof. intros P b s r ch Ps Pr H. destruct b; [injection H as <-; exact Ps | exact (Pr H)]. Qed.

Lemma HS_asan_ok : forall h ch, HS_asan h = Some ch -> hs_all_ok ch = true.
Proof.
  intros h ch. unfold HS_asan.
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_3000|].
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_2000|].
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_1000|].
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_0| discriminate].
Qed.

(* [comment removed for export] *)
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem s3s_A : rt_contracts RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) -> fuzz_one_cps RTA LIB_A ->
  S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof.
  intros RC IOC FUZZ.
  exact (s3s_A_of IT0 IT0_ok HS_asan startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_asan_ok RC IOC FUZZ).
Qed.

(* [comment removed for export] *)
Theorem s3s_A_rc : rt_contracts RTA -> fuzz_one_cps RTA LIB_A ->
  S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof. intros RC FUZZ. exact (s3s_A RC rta_io FUZZ). Qed.

(* [comment removed for export] *)
