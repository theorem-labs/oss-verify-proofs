(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib Require Import FinalP.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import TopBoth.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require AsanBoot AsanMainEntryFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_main_top A_entry_closed.

(* [comment removed for export] *)
Theorem both_assembled_sanitizer_of_side : both_side ->
  strong_universal_error_free_T_budgets Equivalence.SanitizerBudgets.lim_source Equivalence.SanitizerBudgets.lim_target
    src_img both_img.
Proof. intro BOTH. exact (top_both_sanitizer SIP SIP_fp PF_P BOTH). Qed.

(* [comment removed for export] *)
Theorem both_assembled_sanitizer_of_parts : forall MENTRY, both_boot_stmt MENTRY -> both_main_stmt MENTRY ->
  strong_universal_error_free_T_budgets Equivalence.SanitizerBudgets.lim_source Equivalence.SanitizerBudgets.lim_target
    src_img both_img.
Proof. intros MENTRY BOOT MAINS. exact (both_assembled_sanitizer_of_side (both_side_of_parts MENTRY BOOT MAINS)). Qed.

Lemma both_boot : both_boot_stmt AsanMainEntryFacts.main_entry_A.
Proof. exact AsanBoot.asan_boot_entry_inp. Qed.

Theorem both_assembled_sanitizer_of_main : both_main_stmt AsanMainEntryFacts.main_entry_A ->
  strong_universal_error_free_T_budgets Equivalence.SanitizerBudgets.lim_source Equivalence.SanitizerBudgets.lim_target
    src_img both_img.
Proof. intro MAINS. exact (both_assembled_sanitizer_of_parts _ both_boot MAINS). Qed.

Lemma both_main : both_main_stmt AsanMainEntryFacts.main_entry_A.
Proof.
  intros sp brk0 rdraw argv envp fs uid hw Hsp Hva Hve Hfit _ _ R mem md HME Hfs.
  exact (A_main_top.A_main_stmt_of_bridge _ argv fs sp
           (A_entry_closed.entry_bridge_closed sp brk0 rdraw argv envp fs uid hw Hsp Hva Hve Hfit) R mem md HME Hfs).
Qed.


Theorem both_assembled_sanitizer :
  strong_universal_error_free_T_budgets Equivalence.SanitizerBudgets.lim_source Equivalence.SanitizerBudgets.lim_target
    src_img both_img.
Proof. exact (both_assembled_sanitizer_of_parts _ both_boot both_main). Qed.

