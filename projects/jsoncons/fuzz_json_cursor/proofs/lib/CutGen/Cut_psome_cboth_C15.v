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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_psome_cboth_T Cut_psome_cboth_R0p0 Cut_psome_cboth_R0p1 Cut_psome_cboth_R0p2 Cut_psome_cboth_R0p3 Cut_psome_cboth_R1p0 Cut_psome_cboth_R1p1 Cut_psome_cboth_R1p2 Cut_psome_cboth_R1p3 Cut_psome_cboth_R1p4 Cut_psome_cboth_R1p5 Cut_psome_cboth_R1p6 Cut_psome_cboth_R1p7 Cut_psome_cboth_R1p8 Cut_psome_cboth_R1p9 Cut_psome_cboth_R1p10 Cut_psome_cboth_R1p11 Cut_psome_cboth_R1p12 Cut_psome_cboth_R1p13 Cut_psome_cboth_R1p14 Cut_psome_cboth_R1p15 Cut_psome_cboth_R1p16 Cut_psome_cboth_R2p0 Cut_psome_cboth_R2p1 Cut_psome_cboth_R2p2 Cut_psome_cboth_R2p3 Cut_psome_cboth_R2p4 Cut_psome_cboth_R2p5 Cut_psome_cboth_R3p0 Cut_psome_cboth_R3p1 Cut_psome_cboth_D.
Lemma cert150 : as0_cut_cert ITR BF cp150 (CA.po_ops o150) (CA.po_ops2 o150) (CA.po_plan o150) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert151 : as0_cut_cert ITR BF cp151 (CA.po_ops o151) (CA.po_ops2 o151) (CA.po_plan o151) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert152 : as0_cut_cert ITR BF cp152 (CA.po_ops o152) (CA.po_ops2 o152) (CA.po_plan o152) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert153 : as0_cut_cert ITR BF cp153 (CA.po_ops o153) (CA.po_ops2 o153) (CA.po_plan o153) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert154 : as0_cut_cert ITR BF cp154 (CA.po_ops o154) (CA.po_ops2 o154) (CA.po_plan o154) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert155 : as0_cut_cert ITR BF cp155 (CA.po_ops o155) (CA.po_ops2 o155) (CA.po_plan o155) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert156 : as0_cut_cert ITR BF cp156 (CA.po_ops o156) (CA.po_ops2 o156) (CA.po_plan o156) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert157 : as0_cut_cert ITR BF cp157 (CA.po_ops o157) (CA.po_ops2 o157) (CA.po_plan o157) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert158 : as0_cut_cert ITR BF cp158 (CA.po_ops o158) (CA.po_ops2 o158) (CA.po_plan o158) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert159 : as0_cut_cert ITR BF cp159 (CA.po_ops o159) (CA.po_ops2 o159) (CA.po_plan o159) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
