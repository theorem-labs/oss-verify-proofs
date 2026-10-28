(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AMain_final AZ_client AZ_closed_inst.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem base_asan_closed :
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage bsegs b_init_pc b_phdrs).
Proof. apply base_both_of_client; apply client_closed. Qed.

Theorem base_both_plain_closed :
  strong_universal_error_free_T_scfg (alloc_only_cfg false)
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage bsegs b_init_pc b_phdrs).
Proof. apply base_both_plain_of_client; apply client_closed. Qed.
