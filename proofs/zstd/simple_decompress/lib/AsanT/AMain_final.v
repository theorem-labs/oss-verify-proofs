(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Import AsanMain AsanMainB.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF AMain_closed AMain_closedI AFreeAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition client_stmt : Prop := forall rc : runConstT, fuzz_oneA_stmt (AI_of (@AHI_free rc)) AFake_iface.afake_rng.

Theorem both_impl_final : client_stmt -> both_impl_stmt ASTAGE.
Proof. intros CLIENT. exact (both_impl_of_free (fun rc : runConstT => @AHI_free rc) CLIENT). Qed.

Theorem base_both_of_client : client_stmt ->
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage bsegs b_init_pc b_phdrs).
Proof. intros CLIENT. exact (base_both ASTAGE (both_impl_final CLIENT)). Qed.

Theorem base_both_plain_of_client : client_stmt ->
  strong_universal_error_free_T_scfg (alloc_only_cfg false)
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage bsegs b_init_pc b_phdrs).
Proof. intros CLIENT. exact (base_both_plain ASTAGE (both_impl_final CLIENT)). Qed.
