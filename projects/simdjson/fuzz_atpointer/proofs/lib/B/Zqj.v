(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks D_defs D_kit Zpm Zpl Zq2 Sj_rtf
  Zqc Zqd Zsl Zqf Zsv Zvp Zvq Zs4 Zsj Zsi.
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
