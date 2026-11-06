(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit D_libiface Sj_rtf Sj_new Sj_stage1 Atp_h_defsA Atp_activewA Atp_activeA
  Od_hkit0A Od_createA Od_splitintoA Od_topA Od_errx_defsA Od_s1zA
  Od_setup_defsA Od_setup_defs2A Od_setupaA Od_setupbA Od_setupw4A Od_setupcA Od_setupdA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Setup.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis NEWA : new_cps RT e_newarr_nt.
Hypothesis SPL : splitinto_cps0A RT.
Hypothesis EMP : empl_cpsA RT.
Hypothesis GETACT : getact_cps RT.
Hypothesis CREATE : create_cps RT.
Hypothesis HS1 : stage1_cps RT.
Hypothesis HS1Z : stage1z_cps RT.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.
Hypothesis AFI : forall Σ m, ART RT Σ m -> vt_impl m.
Hypothesis ERRX : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_errx_stmt RT sj_lib PMc.
Hypothesis HANDOVER : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_handover_stmt RT sj_lib PMc.

Theorem od_setup : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_setup_stmt RT sj_lib PMc.
Proof using AF RTF NEWA SPL EMP GETACT CREATE HS1 HS1Z AFC AFV AFI ERRX HANDOVER.
  intros PMc FDO MST.
  apply (od_setup_of_phases RT sj_lib PMc).
  - exact (od_phaseA RT sj_lib sj_lib_loc AF PMc FDO MST RTF SPL EMP).
  - exact (od_phaseB RT sj_lib sj_lib_loc AF PMc FDO MST RTF NEWA AFC).
  - apply (od_phaseC_of RT sj_lib PMc).
    + exact (od_phaseC1 RT AF PMc FDO MST RTF NEWA AFC AFV AFI GETACT CREATE HS1 HS1Z).
    + exact (od_phaseC2 RT sj_lib PMc AF MST (ERRX PMc FDO MST) (HANDOVER PMc FDO MST)).
Qed.

End Setup.
