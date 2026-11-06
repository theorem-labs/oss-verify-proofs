(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import AsanMain HaltsAsanB.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import ProgExits.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ADriver_iface AMain_final AH_fi_final.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem halts_asanB : halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source EXITS02 (mkImage asegs a_init_pc a_phdrs).
Proof. exact (halts_asanB_of_impl ASTAGE (asan_impl_final AH_fi_final.fuzz_client_closed) forced_only_cfg (forced_only_cfg_least _)). Qed.
