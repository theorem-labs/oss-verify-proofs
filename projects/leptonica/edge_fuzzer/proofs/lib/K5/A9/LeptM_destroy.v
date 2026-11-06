(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf Lept_chain LeptM_destroy_defs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require LeptM_destroy_c0_1_1 LeptM_destroy_c0_1_0 LeptM_destroy_c0_0_1 LeptM_destroy_c0_0_0 LeptM_destroy_c16_1_1 LeptM_destroy_c16_1_0 LeptM_destroy_c16_0_1 LeptM_destroy_c16_0_0.
Import ListNotations.
Open Scope Z_scope.
Section DESTROY_FINAL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis CMD : pixcmapDestroy_cps RT.

Theorem pixDestroy_ok : pixDestroy_cps RT.
Proof using AF GP CMD.
  apply pixDestroy_of_cases; intros [|] [|].
  - exact (LeptM_destroy_c0_1_1.pixDestroy_case_ok RT AF GP CMD).
  - exact (LeptM_destroy_c0_1_0.pixDestroy_case_ok RT AF GP CMD).
  - exact (LeptM_destroy_c0_0_1.pixDestroy_case_ok RT AF GP CMD).
  - exact (LeptM_destroy_c0_0_0.pixDestroy_case_ok RT AF GP CMD).
  - exact (LeptM_destroy_c16_1_1.pixDestroy_case_ok RT AF GP CMD).
  - exact (LeptM_destroy_c16_1_0.pixDestroy_case_ok RT AF GP CMD).
  - exact (LeptM_destroy_c16_0_1.pixDestroy_case_ok RT AF GP CMD).
  - exact (LeptM_destroy_c16_0_0.pixDestroy_case_ok RT AF GP CMD).
Qed.
End DESTROY_FINAL.
