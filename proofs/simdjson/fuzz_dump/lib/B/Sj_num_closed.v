(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bdefs Sj_num_lits Sj_num_wrap Sj_num_wrap2 Sj_num_fc_stmt Sj_num_ff_top Sj_num_ff_pn3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem ffb_closed : forall RT, art_facts RT ->
  (forall PMc, fdfs_only PMc -> mat_stable PMc -> fcb_stmt RT PMc) ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> ffb_stmt RT PMc.
Proof. intros RT AF HFC PMc FDO MST. exact (ffb_ok RT AF (num_lits_of_af RT AF) PMc FDO MST (HFC PMc FDO MST)). Qed.

Theorem slowfa_closed : forall RT, art_facts RT -> rt_contracts_f RT ->
  (forall PMc, fdfs_only PMc -> mat_stable PMc -> fcb_stmt RT PMc) -> slowfa_cps RT.
Proof. intros RT AF RTF HFC. exact (slowfa_ok RT AF RTF (ffb_closed RT AF HFC)). Qed.

Theorem pffa_closed : forall RT, art_facts RT -> rt_contracts_f RT ->
  (forall PMc, fdfs_only PMc -> mat_stable PMc -> fcb_stmt RT PMc) -> pffa_cps RT.
Proof. intros RT AF RTF HFC. exact (pffa_ok RT AF RTF (ffb_closed RT AF HFC)). Qed.
