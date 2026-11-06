(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_libiface Sj_rtf Sj_new Atp_h_defsA Atp_activewA Atp_activeA
  Sj_stage1_iface Od_hkit0A Od_createA Od_deldtorA Od_splitintoB Od_top_defsB Od_s1zB
  Od_setup_defsB Od_setup_defs2B Od_setupaB Od_setupbB Od_setupw4B Od_setupc1B Od_hand_defsB Od_setupdB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Setup.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis NEWA : new_cps RT e_newarr_nt.
Hypothesis SPL : splitinto_cps0A RT.
Hypothesis EMPS : empls_cpsA RT.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.
Hypothesis PC1 : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_phaseC1_stmt RT sj_lib PMc.
Hypothesis PC2 : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_phaseC2_stmt RT sj_lib PMc.

Theorem od_setup_of_c : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_setup_stmt RT sj_lib PMc.
Proof using AF RTF NEWA SPL EMPS AFC PC1 PC2.
  intros PMc FDO MST.
  apply (od_setup_of_phases RT sj_lib PMc).
  - exact (od_phaseA RT sj_lib sj_lib_loc AF PMc FDO MST RTF SPL EMPS).
  - exact (od_phaseB RT sj_lib sj_lib_loc AF PMc FDO MST RTF NEWA AFC).
  - apply (od_phaseC_of RT sj_lib PMc).
    + exact (PC1 PMc FDO MST).
    + exact (PC2 PMc FDO MST).
Qed.

End Setup.

Section SetupClosed.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis NEWA : new_cps RT e_newarr_nt.
Hypothesis DELA : del_cps RT e_delarr.
Hypothesis DTOR : deldtor_cps RT.
Hypothesis VDES : vdestroy_cpsA RT.
Hypothesis SPL : splitinto_cps0A RT.
Hypothesis EMPS : empls_cpsA RT.
Hypothesis GETACT : getact_cps RT.
Hypothesis CREATE : create_cps RT.
Hypothesis HS1 : stage1_cps RT.
Hypothesis HS1Z : stage1z_cps RT.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.
Hypothesis AFI : forall Σ m, ART RT Σ m -> vt_impl m.
Hypothesis HANDOVER : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_handover_stmt RT sj_lib PMc.

Theorem od_setup : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_setup_stmt RT sj_lib PMc.
Proof using AF RTF NEWA DELA DTOR VDES SPL EMPS GETACT CREATE HS1 HS1Z AFC AFV AFI HANDOVER.
  apply (od_setup_of_c RT AF RTF NEWA SPL EMPS AFC).
  - intros PMc FDO MST. exact (od_phaseC1 RT AF PMc FDO MST RTF NEWA AFC AFV AFI GETACT CREATE HS1 HS1Z).
  - intros PMc FDO MST. exact (od_phaseC2 RT sj_lib PMc AF sj_lib_loc FDO MST RTF DELA DTOR VDES AFV (HANDOVER PMc FDO MST)).
Qed.

End SetupClosed.
