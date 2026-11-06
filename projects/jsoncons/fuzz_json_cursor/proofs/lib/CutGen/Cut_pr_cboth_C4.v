(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm9PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_pr_cboth_T Cut_pr_cboth_R0p0 Cut_pr_cboth_R0p1 Cut_pr_cboth_R0p2 Cut_pr_cboth_R0p3 Cut_pr_cboth_R0p4 Cut_pr_cboth_R1p0 Cut_pr_cboth_R1p1 Cut_pr_cboth_R2p0 Cut_pr_cboth_R2p1 Cut_pr_cboth_D.
Lemma cert32 : as0_cut_cert ITR BF cp32 (CA.po_ops o32) (CA.po_ops2 o32) (CA.po_plan o32) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert33 : as0_cut_cert ITR BF cp33 (CA.po_ops o33) (CA.po_ops2 o33) (CA.po_plan o33) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert34 : as0_cut_cert ITR BF cp34 (CA.po_ops o34) (CA.po_ops2 o34) (CA.po_plan o34) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert35 : as0_cut_cert ITR BF cp35 (CA.po_ops o35) (CA.po_ops2 o35) (CA.po_plan o35) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert36 : as0_cut_cert ITR BF cp36 (CA.po_ops o36) (CA.po_ops2 o36) (CA.po_plan o36) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert37 : as0_cut_cert ITR BF cp37 (CA.po_ops o37) (CA.po_ops2 o37) (CA.po_plan o37) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert38 : as0_cut_cert ITR BF cp38 (CA.po_ops o38) (CA.po_ops2 o38) (CA.po_plan o38) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert39 : as0_cut_cert ITR BF cp39 (CA.po_ops o39) (CA.po_ops2 o39) (CA.po_plan o39) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
