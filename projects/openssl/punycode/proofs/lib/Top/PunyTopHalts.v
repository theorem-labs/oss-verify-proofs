(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
Require OSSVerify.openssl.punycode.images.Plain.
Require OSSVerify.openssl.punycode.images.Ubsan.
Require OSSVerify.openssl.punycode.images.Asan.
Require OSSVerify.openssl.punycode.images.AsanUbsan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import HaltsKit.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import SpecHalts.
From OSSVerify.Proofs.openssl.punycode.lib Require Import Spec.
From OSSVerify.Proofs.openssl.punycode.lib.Top Require Import TopBridge ImageHalts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PI := OSSVerify.openssl.punycode.images.Plain.M.
Module UI := OSSVerify.openssl.punycode.images.Ubsan.M.
Module AI := OSSVerify.openssl.punycode.images.Asan.M.
Module BI := OSSVerify.openssl.punycode.images.AsanUbsan.M.

(* [comment removed for export] *)
Definition P_realizes := image_realizes PI.loaded_segments PI.init_pc PI.phdrs source_alloc_limit Spec.spec.
Definition U_realizes := image_realizes UI.loaded_segments UI.init_pc UI.phdrs target_alloc_limit Spec.spec.
Definition A_realizes := image_realizes AI.loaded_segments AI.init_pc AI.phdrs target_alloc_limit Spec.spec.
Definition B_realizes := image_realizes BI.loaded_segments BI.init_pc BI.phdrs target_alloc_limit Spec.spec.

Lemma halts_plain : P_realizes ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source spec_codes (mkImage PI.loaded_segments PI.init_pc PI.phdrs).
Proof.
  intros H.
  exact (image_halts_budgets PI.loaded_segments PI.init_pc PI.phdrs Spec.spec spec_codes spec_exits_in spec_kill_free
           source_alloc_limit source_alloc_limit lim_source_le_source H).
Qed.

Lemma halts_ubsan : U_realizes ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source spec_codes (mkImage UI.loaded_segments UI.init_pc UI.phdrs).
Proof.
  intros H.
  exact (image_halts_budgets UI.loaded_segments UI.init_pc UI.phdrs Spec.spec spec_codes spec_exits_in spec_kill_free
           target_alloc_limit source_alloc_limit lim_source_le_target H).
Qed.

Lemma halts_asan : A_realizes ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source spec_codes (mkImage AI.loaded_segments AI.init_pc AI.phdrs).
Proof.
  intros H.
  exact (image_halts_budgets AI.loaded_segments AI.init_pc AI.phdrs Spec.spec spec_codes spec_exits_in spec_kill_free
           target_alloc_limit source_alloc_limit lim_source_le_target H).
Qed.

Lemma halts_both : B_realizes ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source spec_codes (mkImage BI.loaded_segments BI.init_pc BI.phdrs).
Proof.
  intros H.
  exact (image_halts_budgets BI.loaded_segments BI.init_pc BI.phdrs Spec.spec spec_codes spec_exits_in spec_kill_free
           target_alloc_limit source_alloc_limit lim_source_le_target H).
Qed.

(* [comment removed for export] *)
Definition P_halts := lane_halts forced_only_cfg PI.loaded_segments PI.init_pc PI.phdrs source_alloc_limit spec_codes.
Definition U_halts := lane_halts forced_only_cfg UI.loaded_segments UI.init_pc UI.phdrs source_alloc_limit spec_codes.

Lemma halts_plain_of_lane : P_halts ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source spec_codes (mkImage PI.loaded_segments PI.init_pc PI.phdrs).
Proof. intros HP. exact (halts_allowed_of_lane _ _ _ _ _ _ HP). Qed.

Lemma halts_ubsan_of_lane : U_halts ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source spec_codes (mkImage UI.loaded_segments UI.init_pc UI.phdrs).
Proof. intros HU. exact (halts_allowed_of_lane _ _ _ _ _ _ HU). Qed.
