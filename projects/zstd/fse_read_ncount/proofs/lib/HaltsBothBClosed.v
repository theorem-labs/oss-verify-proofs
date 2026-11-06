(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import BothMain HaltsBothB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import ProgExits.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ADriver_iface AMain_final AH_fse_final.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem halts_bothB : halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source EXITS02 (mkImage bsegs b_init_pc b_phdrs).
Proof. exact (halts_bothB_of_impl ASTAGE (both_impl_final AH_fse_final.fuzz_client_closed) forced_only_cfg (forced_only_cfg_least ACFG)). Qed.
