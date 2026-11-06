(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Zks Sj_rtf Zqc Zqf Zti Zv1 Zu3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem lmb_closed : forall RT, art_facts RT -> rt_contracts_f RT -> forall PMc, fdfs_only PMc -> mat_stable PMc -> lmb_stmt RT PMc.
Proof. exact lmb_ok. Qed.

Theorem p5b_closed : forall RT, art_facts RT -> rt_contracts_f RT -> forall PMc, fdfs_only PMc -> mat_stable PMc -> p5b_stmt RT PMc.
Proof. intros RT AF RTF PMc FDO MST. exact (p5b_ok RT AF RTF PMc FDO MST (lmb_ok RT AF RTF PMc FDO MST)). Qed.

Theorem pdcb_closed : forall RT, art_facts RT -> rt_contracts_f RT -> forall PMc, fdfs_only PMc -> mat_stable PMc -> pdcb_stmt RT PMc.
Proof. intros RT AF RTF PMc FDO MST. exact (pdcb_ok RT AF RTF PMc FDO MST (p5b_closed RT AF RTF PMc FDO MST)). Qed.
