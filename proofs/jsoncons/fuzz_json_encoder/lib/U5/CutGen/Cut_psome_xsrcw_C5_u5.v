(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5 ParseSums2X_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX SmallKnX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_psome_xsrcw_T_u5 Cut_psome_xsrcw_R0_u5 Cut_psome_xsrcw_R1p0_u5 Cut_psome_xsrcw_R1p1_u5 Cut_psome_xsrcw_R1p2_u5 Cut_psome_xsrcw_R1p3_u5 Cut_psome_xsrcw_R1p4_u5 Cut_psome_xsrcw_R2_u5 Cut_psome_xsrcw_R3_u5 Cut_psome_xsrcw_D_u5.
Lemma cert200 : src0_cut_cert ITR BF cp200 (CA.po_ops o200) (CA.po_ops2 o200) (CA.po_plan o200) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert201 : src0_cut_cert ITR BF cp201 (CA.po_ops o201) (CA.po_ops2 o201) (CA.po_plan o201) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
