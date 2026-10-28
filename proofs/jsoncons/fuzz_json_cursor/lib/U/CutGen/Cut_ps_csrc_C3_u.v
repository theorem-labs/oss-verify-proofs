(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums3C_u.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_ps_csrc_T_u Cut_ps_csrc_R0_u Cut_ps_csrc_R1p0_u Cut_ps_csrc_R1p1_u Cut_ps_csrc_R2_u Cut_ps_csrc_R3_u Cut_ps_csrc_R4_u Cut_ps_csrc_D_u.
Lemma cert120 : src0_cut_cert ITR BF cp120 (CA.po_ops o120) (CA.po_ops2 o120) (CA.po_plan o120) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert121 : src0_cut_cert ITR BF cp121 (CA.po_ops o121) (CA.po_ops2 o121) (CA.po_plan o121) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert122 : src0_cut_cert ITR BF cp122 (CA.po_ops o122) (CA.po_ops2 o122) (CA.po_plan o122) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
