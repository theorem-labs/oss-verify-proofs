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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_pn_csrc_T_u Cut_pn_csrc_R0_u Cut_pn_csrc_R1_u Cut_pn_csrc_R2_u Cut_pn_csrc_D_u.
Lemma cert40 : src0_cut_cert ITR BF cp40 (CA.po_ops o40) (CA.po_ops2 o40) (CA.po_plan o40) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert41 : src0_cut_cert ITR BF cp41 (CA.po_ops o41) (CA.po_ops2 o41) (CA.po_plan o41) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert42 : src0_cut_cert ITR BF cp42 (CA.po_ops o42) (CA.po_ops2 o42) (CA.po_plan o42) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert43 : src0_cut_cert ITR BF cp43 (CA.po_ops o43) (CA.po_ops2 o43) (CA.po_plan o43) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert44 : src0_cut_cert ITR BF cp44 (CA.po_ops o44) (CA.po_ops2 o44) (CA.po_plan o44) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert45 : src0_cut_cert ITR BF cp45 (CA.po_ops o45) (CA.po_ops2 o45) (CA.po_plan o45) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert46 : src0_cut_cert ITR BF cp46 (CA.po_ops o46) (CA.po_ops2 o46) (CA.po_plan o46) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert47 : src0_cut_cert ITR BF cp47 (CA.po_ops o47) (CA.po_ops2 o47) (CA.po_plan o47) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert48 : src0_cut_cert ITR BF cp48 (CA.po_ops o48) (CA.po_ops2 o48) (CA.po_plan o48) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
