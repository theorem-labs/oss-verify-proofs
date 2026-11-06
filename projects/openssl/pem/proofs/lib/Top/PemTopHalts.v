(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
Require OSSVerify.openssl.pem.images.Plain.
Require OSSVerify.openssl.pem.images.Ubsan.
Require OSSVerify.openssl.pem.images.Asan.
Require OSSVerify.openssl.pem.images.AsanUbsan.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import HaltsKit.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import SpecHalts.
From OSSVerify.Proofs.openssl.pem.lib Require Import Spec.
From OSSVerify.Proofs.openssl.pem.lib.Top Require Import TopBridge ImageHalts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_realizes := image_realizes OSSVerify.openssl.pem.images.Plain.M.loaded_segments OSSVerify.openssl.pem.images.Plain.M.init_pc OSSVerify.openssl.pem.images.Plain.M.phdrs source_alloc_limit Spec.spec.
Definition U_realizes := image_realizes OSSVerify.openssl.pem.images.Ubsan.M.loaded_segments OSSVerify.openssl.pem.images.Ubsan.M.init_pc OSSVerify.openssl.pem.images.Ubsan.M.phdrs target_alloc_limit Spec.spec.
Definition A_realizes := image_realizes OSSVerify.openssl.pem.images.Asan.M.loaded_segments OSSVerify.openssl.pem.images.Asan.M.init_pc OSSVerify.openssl.pem.images.Asan.M.phdrs target_alloc_limit Spec.spec.
Definition B_realizes := image_realizes OSSVerify.openssl.pem.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.pem.images.AsanUbsan.M.init_pc OSSVerify.openssl.pem.images.AsanUbsan.M.phdrs target_alloc_limit Spec.spec.

Lemma halts_plain : P_realizes ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source spec_codes (mkImage OSSVerify.openssl.pem.images.Plain.M.loaded_segments OSSVerify.openssl.pem.images.Plain.M.init_pc OSSVerify.openssl.pem.images.Plain.M.phdrs).
Proof.
  intros H.
  exact (image_halts_budgets OSSVerify.openssl.pem.images.Plain.M.loaded_segments OSSVerify.openssl.pem.images.Plain.M.init_pc OSSVerify.openssl.pem.images.Plain.M.phdrs Spec.spec spec_codes spec_exits_in spec_kill_free
           source_alloc_limit source_alloc_limit lim_source_le_source H).
Qed.

Lemma halts_ubsan : U_realizes ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source spec_codes (mkImage OSSVerify.openssl.pem.images.Ubsan.M.loaded_segments OSSVerify.openssl.pem.images.Ubsan.M.init_pc OSSVerify.openssl.pem.images.Ubsan.M.phdrs).
Proof.
  intros H.
  exact (image_halts_budgets OSSVerify.openssl.pem.images.Ubsan.M.loaded_segments OSSVerify.openssl.pem.images.Ubsan.M.init_pc OSSVerify.openssl.pem.images.Ubsan.M.phdrs Spec.spec spec_codes spec_exits_in spec_kill_free
           target_alloc_limit source_alloc_limit lim_source_le_target H).
Qed.

Lemma halts_asan : A_realizes ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source spec_codes (mkImage OSSVerify.openssl.pem.images.Asan.M.loaded_segments OSSVerify.openssl.pem.images.Asan.M.init_pc OSSVerify.openssl.pem.images.Asan.M.phdrs).
Proof.
  intros H.
  exact (image_halts_budgets OSSVerify.openssl.pem.images.Asan.M.loaded_segments OSSVerify.openssl.pem.images.Asan.M.init_pc OSSVerify.openssl.pem.images.Asan.M.phdrs Spec.spec spec_codes spec_exits_in spec_kill_free
           target_alloc_limit source_alloc_limit lim_source_le_target H).
Qed.

Lemma halts_both : B_realizes ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source spec_codes (mkImage OSSVerify.openssl.pem.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.pem.images.AsanUbsan.M.init_pc OSSVerify.openssl.pem.images.AsanUbsan.M.phdrs).
Proof.
  intros H.
  exact (image_halts_budgets OSSVerify.openssl.pem.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.pem.images.AsanUbsan.M.init_pc OSSVerify.openssl.pem.images.AsanUbsan.M.phdrs Spec.spec spec_codes spec_exits_in spec_kill_free
           target_alloc_limit source_alloc_limit lim_source_le_target H).
Qed.
