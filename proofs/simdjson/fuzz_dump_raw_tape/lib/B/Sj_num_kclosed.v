(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import RT_iface Sj_rtf Sj_num_akit Sj_num_bdefs Sj_num_lm_top3 Sj_num_pow5_top Sj_num_pdc_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem lmb_closed : forall RT, art_facts RT -> rt_contracts_f RT -> forall PMc, fdfs_only PMc -> mat_stable PMc -> lmb_stmt RT PMc.
Proof. exact lmb_ok. Qed.

Theorem p5b_closed : forall RT, art_facts RT -> rt_contracts_f RT -> forall PMc, fdfs_only PMc -> mat_stable PMc -> p5b_stmt RT PMc.
Proof. intros RT AF RTF PMc FDO MST. exact (p5b_ok RT AF RTF PMc FDO MST (lmb_ok RT AF RTF PMc FDO MST)). Qed.

Theorem pdcb_closed : forall RT, art_facts RT -> rt_contracts_f RT -> forall PMc, fdfs_only PMc -> mat_stable PMc -> pdcb_stmt RT PMc.
Proof. intros RT AF RTF PMc FDO MST. exact (pdcb_ok RT AF RTF PMc FDO MST (p5b_closed RT AF RTF PMc FDO MST)). Qed.
