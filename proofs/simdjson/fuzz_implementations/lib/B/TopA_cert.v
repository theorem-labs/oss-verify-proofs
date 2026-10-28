(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import Plain.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanTablesB AsanStartupB StartupHSBoth StartupPlanBoth BothStartupCert.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import RT_iface RT_iface2 RT_rep D_defs I_iodefs X_xdefs Imp_libifaceA Imp_handoffA TopA_iodefs RT_io TopA_start TopA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib Require Import TopLevelA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib Require Import ProofBase.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib Require Spec.ProgNoEnomem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.
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

Section Main.

Hypothesis MAIN : forall argv fs, valid_argv argv -> forall c, START RTA OUT_repA ERR_repA XENVA (imp_libA None) argv fs c -> realizes bsegs c (canonT (argv_Z argv) fs).

Theorem s3s_A : S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof using MAIN.
  exact (s3s_A_of IT0 IT0_ok HS_both startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_both_ok HS_imp_ok MAIN).
Qed.

Theorem base_asan_of : impl_P_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof using MAIN.
  intros HP.
  exact (base_asan_of_cert IT0 IT0_ok HS_both startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_both_ok HS_imp_ok MAIN
           HP Spec.ProgNoEnomem.prog_no_enomem_P).
Qed.
End Main.
