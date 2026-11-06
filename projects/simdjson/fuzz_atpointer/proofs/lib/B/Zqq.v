(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Zks Sj_rtf Zqc Zqf Zs4 Zr0 Zr4 Zrh Zrp
  Zrs Zqw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem fcb_closed : forall RT, art_facts RT -> rt_contracts_f RT -> forall PMc, fdfs_only PMc -> mat_stable PMc -> fcb_stmt RT PMc.
Proof.
  apply fcb_closed_gen. intros E' Q OK PV K14 KERR. exact (fcb_parse E' OK PV Q K14 KERR).
Qed.
