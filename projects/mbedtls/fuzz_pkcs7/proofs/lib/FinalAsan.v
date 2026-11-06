(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib Require Import FinalP TopAsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_entry_closed.

Lemma asan_bridge : asan_bridge_stmt.
Proof.
  intros sp brk0 rdraw argv envp fs uid hw Hsp Hva Hve Hfit _ _.
  exact (A_entry_closed.entry_bridge_closed sp brk0 rdraw argv envp fs uid hw Hsp Hva Hve Hfit).
Qed.

(* [comment removed for export] *)
Theorem asan_assembled : strong_universal_error_free_T src_img asan_img.
Proof. exact (top_asan SIP SIP_fp PF_P asan_bridge). Qed.

(* [comment removed for export] *)
Theorem asan_assembled_sanitizer :
  strong_universal_error_free_T_budgets Equivalence.SanitizerBudgets.lim_source Equivalence.SanitizerBudgets.lim_target
    src_img asan_img.
Proof. exact (top_asan_sanitizer SIP SIP_fp PF_P asan_bridge). Qed.
