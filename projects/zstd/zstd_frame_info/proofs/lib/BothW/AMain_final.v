(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import BothMain.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF AMain_closed AMain_closedI AFreeAll.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Require OSSVerify.Proofs.zstd.zstd_frame_info.lib.PlainTree.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition client_stmt : Prop := forall rc : runConstT, fuzz_oneA_stmt (AI_of (@AHI_free rc)) AFake_iface.afake_rng.

Theorem both_impl_final : client_stmt -> both_impl_stmt ASTAGE.
Proof. intros CLIENT. exact (both_impl_of_free (fun rc : runConstT => @AHI_free rc) CLIENT). Qed.

(* [comment removed for export] *)
Theorem base_both_of_client : plain_tree_ok_stmt -> client_stmt ->
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage bsegs b_init_pc b_phdrs).
Proof. intros PLAIN CLIENT. exact (base_both ASTAGE PLAIN (both_impl_final CLIENT)). Qed.

(* [comment removed for export] *)
