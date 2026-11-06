(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Ceiling Cfg.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib Require Import TopLevel Obligations ProofBase TopLevelA TopE TopSides TopFinal_plain.
From OSSVerify.simdjson.fuzz_dump_raw_tape.images Require Import Plain.
From OSSVerify.simdjson.fuzz_dump_raw_tape.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem off_asan_cfg : client_P_stmt -> S3s_stmt_e Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs ->
  strong_universal_error_free_T_scfg ACFG (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. intros CP HA. exact (asanfam_off (HP CP) _ _ _ HA). Qed.
Theorem base_asan_cfg : client_P_stmt -> S3s_stmt_e Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs ->
  strong_universal_error_free_T_scfg_budgets_abort ACFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. intros CP HA. exact (asanfam_base_san (HP CP) _ _ _ HA). Qed.

