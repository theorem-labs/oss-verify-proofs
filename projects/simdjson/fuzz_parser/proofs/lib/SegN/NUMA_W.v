(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface AFake_iface AHarnessU_iface AInstanceW2 AHarnessP_closed2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import PA2_main.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPA_sum NUMA_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Theorem sumw_SFPAS : SUMW_T AI_W afake_rng SFPAS.
Proof. intros L RNG st LB data idxs F. exact (NTOP.sumw_sfpa _ L RNG st LB F). Qed.
Theorem sumw_PFFAS : SUMW_T AI_W afake_rng PFFAS.
Proof. intros L RNG st LB data idxs F. exact (NTOP.sumw_pffa _ L RNG st LB F). Qed.
Theorem sumc_SFPCAS : SUMC_T AI_W afake_rng SFPCAS.
Proof. intros L RNG st LB data idxs F p COPY n. exact (NTOP.sumc_sfpca _ L RNG st LB F p COPY n). Qed.
Theorem sumc_PFFCAS : SUMC_T AI_W afake_rng PFFCAS.
Proof. intros L RNG st LB data idxs F p COPY n. exact (NTOP.sumc_pffca _ L RNG st LB F p COPY n). Qed.

(* [comment removed for export] *)
Theorem fuzz_closedW : fuzz_oneU_stmt AI_W afake_rng.
Proof. exact (fuzz_closedW_mod_num sumw_SFPAS sumw_PFFAS sumc_SFPCAS sumc_PFFCAS). Qed.
End CANSEC1.
Print Assumptions fuzz_closedW.
