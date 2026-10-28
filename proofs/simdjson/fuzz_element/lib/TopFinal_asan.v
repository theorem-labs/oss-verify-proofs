(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling Cfg.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib Require Import TopLevel Obligations ProofBase TopLevelA TopE TopSides TopFinal_plain.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Plain.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem off_asan_cfg : client_P_stmt -> S3s_stmt_e Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs ->
  strong_universal_error_free_T_scfg ACFG (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. intros CP HA. exact (asanfam_off (HP CP) _ _ _ HA). Qed.
Theorem base_asan_cfg : client_P_stmt -> S3s_stmt_e Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs ->
  strong_universal_error_free_T_scfg_budgets_abort ACFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. intros CP HA. exact (asanfam_base_san (HP CP) _ _ _ HA). Qed.
