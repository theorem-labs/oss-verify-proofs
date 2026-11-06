(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs Lept_iface Gm_iface Fh_iface Fh_lowkit
  FhB_low0 FhB_low1 FhB_low2 FhB_low3 FhB_low4 FhB_low5 FhB_low6 FhB_low7 FhB_low8 FhB_low9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FHLOW.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem fhmtgen_low_1_ok : fhmtgen_low_1_cps RT.
Proof using AF GP.
  apply fhmtgen_low_1_of_cases.
  - exact (fhl0_ok RT AF GP).
  - exact (fhl1_ok RT AF GP).
  - exact (fhl2_ok RT AF GP).
  - exact (fhl3_ok RT AF GP).
  - exact (fhl4_ok RT AF GP).
  - exact (fhl5_ok RT AF GP).
  - exact (fhl6_ok RT AF GP).
  - exact (fhl7_ok RT AF GP).
  - exact (fhl8_ok RT AF GP).
  - exact (fhl9_ok RT AF GP).
Qed.
End FHLOW.
