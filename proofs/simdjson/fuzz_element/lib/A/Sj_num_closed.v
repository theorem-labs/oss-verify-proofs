(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_lits Sj_num_wrap Sj_num_wrap2 Sj_num_fc_stmt Sj_num_ff_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem ffa_closed : forall RT, art_facts RT ->
  (forall PMc, fdfs_only PMc -> mat_stable PMc -> fca_stmt RT PMc) ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> ffa_stmt RT PMc.
Proof. intros RT AF HFC PMc FDO MST. exact (ffa_ok RT AF (num_lits_of_af RT AF) PMc FDO MST (HFC PMc FDO MST)). Qed.

Theorem slowfa_closed : forall RT, art_facts RT -> rt_contracts_f RT ->
  (forall PMc, fdfs_only PMc -> mat_stable PMc -> fca_stmt RT PMc) -> slowfa_cps RT.
Proof. intros RT AF RTF HFC. exact (slowfa_ok RT AF RTF (ffa_closed RT AF HFC)). Qed.

Theorem pffa_closed : forall RT, art_facts RT -> rt_contracts_f RT ->
  (forall PMc, fdfs_only PMc -> mat_stable PMc -> fca_stmt RT PMc) -> pffa_cps RT.
Proof. intros RT AF RTF HFC. exact (pffa_ok RT AF RTF (ffa_closed RT AF HFC)). Qed.

