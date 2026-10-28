(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import RT_iface Sj_rtf Sj_num_akit Sj_num_bdefs Sj_num_fc_stmt Sj_num_fc_defs Sj_num_fc_k14 Sj_num_fc_pp1 Sj_num_fc_pp6
  Sj_num_fc_pstmt Sj_num_fc_ctop6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem fcb_closed : forall RT, art_facts RT -> rt_contracts_f RT -> forall PMc, fdfs_only PMc -> mat_stable PMc -> fcb_stmt RT PMc.
Proof.
  apply fcb_closed_gen. intros E' Q OK PV K14 KERR. exact (fcb_parse E' OK PV Q K14 KERR).
Qed.
