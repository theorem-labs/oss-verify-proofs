(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Pm_gaps_iface Pm_iface Pm_iface2 Pm_getters.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Pm_selloop_defs PmL_sel Pm_selcmap_defs Pm_selcmap_tail_c0 Pm_selcmap_tail_c16 Pm_selcmap_al Pm_selcmap_c0 Pm_selcmap_c16.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SELCMAP_TOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis PG : pm_gaps RT.
Hypothesis LSE : lept_stderr_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorInt.
Hypothesis GCM : pixGetColormap_cps RT.
Hypothesis GCNT : pixcmapGetCount_cps RT.
Hypothesis BGG : boxGetGeometry_cps RT.
Hypothesis GIDX : pixcmapGetIndex_cps RT.
Hypothesis ADDC : pixcmapAddColor_cps RT.

Theorem pixSetSelectCmap_ok : pixSetSelectCmap_cps RT.
Proof using AF RC GP PG LSE RERR GCM GCNT BGG GIDX ADDC.
  apply (pixSetSelectCmap_of_al RT).
  - apply (selc_front_ok_0 RT AF RC GP PG LSE RERR GCM GCNT GIDX ADDC).
    intros Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix b v cv fr.
    exact (selc_cut_ok_0 RT AF GP BGG sel_rows_ok Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix b v cv fr).
  - apply (selc_front_ok_16 RT AF RC GP PG LSE RERR GCM GCNT GIDX ADDC).
    intros Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix b v cv fr.
    exact (selc_cut_ok_16 RT AF GP BGG sel_rows_ok Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix b v cv fr).
Qed.
End SELCMAP_TOP.
