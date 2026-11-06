(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_gaps_iface Lept_iface D_iface D_defs D_libiface
  Ed_iface Ed_meas_defs Ed_meas_c0 Ed_meas_c16.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section MEAS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis REI : returnError_cps RT e_returnErrorInt.
Hypothesis PROFILE : pixGetEdgeProfile_cps RT.
Hypothesis EXTREMA : numaFindExtrema_cps RT.
Hypothesis NDESTROY : numaDestroy_cps RT.

Theorem pixMeasureEdgeSmoothness_ok : pixMeasureEdgeSmoothness_cps RT.
Proof using AF RC GP REI PROFILE EXTREMA NDESTROY.
  exact (meas_cases RT (meas_c0 RT AF RC GP REI PROFILE EXTREMA NDESTROY) (meas_c16 RT AF RC GP REI PROFILE EXTREMA NDESTROY)).
Qed.
End MEAS.
