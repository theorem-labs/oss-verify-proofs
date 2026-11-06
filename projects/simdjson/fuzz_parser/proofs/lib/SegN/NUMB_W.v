(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase AMalloc_iface AFake_iface AHarnessU_iface AInstanceW2 AHarnessP_closed2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import PA2_main.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPB_sum NUMB_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Theorem sumw_SFPBS : SUMW_T AI_W afake_rng SFPBS.
Proof. intros L RNG st LB data idxs F. exact (NTOPB.sumw_sfpb _ L RNG st LB F). Qed.
Theorem sumw_PFFBS : SUMW_T AI_W afake_rng PFFBS.
Proof. intros L RNG st LB data idxs F. exact (NTOPB.sumw_pffb _ L RNG st LB F). Qed.
Theorem sumc_SFPCBS : SUMC_T AI_W afake_rng SFPCBS.
Proof. intros L RNG st LB data idxs F p COPY n. exact (NTOPB.sumc_sfpcb _ L RNG st LB F p COPY n). Qed.
Theorem sumc_PFFCBS : SUMC_T AI_W afake_rng PFFCBS.
Proof. intros L RNG st LB data idxs F p COPY n. exact (NTOPB.sumc_pffcb _ L RNG st LB F p COPY n). Qed.

(* [comment removed for export] *)
Theorem fuzz_closedW : fuzz_oneU_stmt AI_W afake_rng.
Proof. exact (fuzz_closedW_mod_num sumw_SFPBS sumw_PFFBS sumc_SFPCBS sumc_PFFCBS). Qed.
End CANSEC1.
(* [comment removed for export] *)
