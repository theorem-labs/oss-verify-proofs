(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan Ubsan AsanUbsan.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Common.BudgetBridge.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.BigintBase.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.BigintAsanFinal.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.BigintBothFinal.

Definition alloc_forced_only_cfg : SpuriousCfg := mkSpuriousCfg false true true true true true.

Theorem fuzz_bigint_asan_agrees :
  strong_universal_error_free_T_scfg_budgets_abort alloc_forced_only_cfg
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc
       Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
  exact (OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Common.BudgetBridge.sue_scfg_abort_shipped_to_sanitizer _ _ _ OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.BigintAsanFinal.fuzz_bigint_asan_base_abort).
Qed.

Theorem fuzz_bigint_ubsan_agrees :
  strong_universal_error_free_T_scfg_budgets_abort alloc_forced_only_cfg
    ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc
       Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.BigintBase.fuzz_bigint_ubsan_base_abort.
Qed.

Theorem fuzz_bigint_asan_ubsan_agrees :
  strong_universal_error_free_T_scfg_budgets_abort alloc_forced_only_cfg
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc
       Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  exact (OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Common.BudgetBridge.sue_scfg_abort_shipped_to_sanitizer _ _ _ OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.BigintBothFinal.fuzz_bigint_both_base_abort).
Qed.
