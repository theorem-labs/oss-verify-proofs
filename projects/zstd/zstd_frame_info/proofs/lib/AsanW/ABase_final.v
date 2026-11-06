(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import AsanMain.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AMain_final AH_fi_final.
Require OSSVerify.Proofs.zstd.zstd_frame_info.lib.PlainTree.

Theorem base_asan_closed :
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage asegs a_init_pc a_phdrs).
Proof. exact (base_asan_of_client PlainTree.plain_tree_ok_L AH_fi_final.fuzz_client_closed). Qed.
