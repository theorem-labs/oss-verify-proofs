(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import RT_iface Sj_rtf Sj_num_akit Sj_num_bdefs Sj_num_kclosed Sj_num_nd_top3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem ndcb_closed : forall RT, art_facts RT -> rt_contracts_f RT -> forall PMc, fdfs_only PMc -> mat_stable PMc -> ndcb_stmt RT PMc.
Proof. intros RT AF RTF PMc FDO MST. exact (ndcb_ok RT AF RTF PMc FDO MST (p5b_closed RT AF RTF PMc FDO MST)). Qed.
