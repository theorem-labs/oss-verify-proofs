(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
Require OssFuzzTheorems.openssl.pem.images.Plain.
Require OssFuzzTheorems.openssl.pem.images.Ubsan.
Require OssFuzzTheorems.openssl.pem.images.Asan.
Require OssFuzzTheorems.openssl.pem.images.AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import CfgStep ShapeEFC.
From OssFuzzTheorems.Proofs.openssl.pem.lib Require Import Spec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Top Require Import TopBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Cls Require Import ClsRows_pem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition P_realizes := image_realizes OssFuzzTheorems.openssl.pem.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Plain.M.init_pc OssFuzzTheorems.openssl.pem.images.Plain.M.phdrs source_alloc_limit Spec.spec.
Definition P_realizes_san := image_realizes OssFuzzTheorems.openssl.pem.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Plain.M.init_pc OssFuzzTheorems.openssl.pem.images.Plain.M.phdrs sanitizer_source_limit Spec.spec.
Definition U_realizes := image_realizes OssFuzzTheorems.openssl.pem.images.Ubsan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Ubsan.M.init_pc OssFuzzTheorems.openssl.pem.images.Ubsan.M.phdrs target_alloc_limit Spec.spec.
Definition A_realizes := image_realizes OssFuzzTheorems.openssl.pem.images.Asan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Asan.M.init_pc OssFuzzTheorems.openssl.pem.images.Asan.M.phdrs target_alloc_limit Spec.spec.
Definition B_realizes := image_realizes OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.init_pc OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.phdrs target_alloc_limit Spec.spec.

Definition CFG := Run.mkSpuriousCfg false true true true true true.

Lemma pinned_ubsan : P_realizes -> U_realizes ->
  strong_universal_error_free_T_scfg CFG (mkImage OssFuzzTheorems.openssl.pem.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Plain.M.init_pc OssFuzzTheorems.openssl.pem.images.Plain.M.phdrs) (mkImage OssFuzzTheorems.openssl.pem.images.Ubsan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Ubsan.M.init_pc OssFuzzTheorems.openssl.pem.images.Ubsan.M.phdrs).
Proof. intros HP HU. exact (pinned_base_of_realizes _ _ _ _ _ _ _ HP HU). Qed.
Lemma pinned_asan : P_realizes -> A_realizes ->
  strong_universal_error_free_T_scfg CFG (mkImage OssFuzzTheorems.openssl.pem.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Plain.M.init_pc OssFuzzTheorems.openssl.pem.images.Plain.M.phdrs) (mkImage OssFuzzTheorems.openssl.pem.images.Asan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Asan.M.init_pc OssFuzzTheorems.openssl.pem.images.Asan.M.phdrs).
Proof. intros HP HA. exact (pinned_base_of_realizes _ _ _ _ _ _ _ HP HA). Qed.
Lemma pinned_both : P_realizes -> B_realizes ->
  strong_universal_error_free_T_scfg CFG (mkImage OssFuzzTheorems.openssl.pem.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Plain.M.init_pc OssFuzzTheorems.openssl.pem.images.Plain.M.phdrs) (mkImage OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.init_pc OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.phdrs).
Proof. intros HP HB. exact (pinned_base_of_realizes _ _ _ _ _ _ _ HP HB). Qed.

(* [comment removed for export] *)
Lemma san_base_asan : P_realizes_san -> A_realizes ->
  strong_universal_error_free_T_scfg_budgets CFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OssFuzzTheorems.openssl.pem.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Plain.M.init_pc OssFuzzTheorems.openssl.pem.images.Plain.M.phdrs) (mkImage OssFuzzTheorems.openssl.pem.images.Asan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Asan.M.init_pc OssFuzzTheorems.openssl.pem.images.Asan.M.phdrs).
Proof. intros HP HA. exact (budgets_base_of_realizes _ _ _ _ _ _ _ _ _ HP HA). Qed.
Lemma san_base_both : P_realizes_san -> B_realizes ->
  strong_universal_error_free_T_scfg_budgets CFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OssFuzzTheorems.openssl.pem.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Plain.M.init_pc OssFuzzTheorems.openssl.pem.images.Plain.M.phdrs) (mkImage OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.init_pc OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.phdrs).
Proof. intros HP HB. exact (budgets_base_of_realizes _ _ _ _ _ _ _ _ _ HP HB). Qed.

(* [comment removed for export] *)
Definition base_ubsan (HP : P_realizes) (HU : U_realizes) := base_row_pem_ubsan CFG (pinned_ubsan HP HU).


Definition base_asan (HPs : P_realizes_san) (HA : A_realizes) := san_base_asan HPs HA.


Definition base_both (HPs : P_realizes_san) (HB : B_realizes) := san_base_both HPs HB.


