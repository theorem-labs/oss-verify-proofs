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
Lemma cert160 : as0_cut_cert ITR BF cp160 (CA.po_ops o160) (CA.po_ops2 o160) (CA.po_plan o160) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert161 : as0_cut_cert ITR BF cp161 (CA.po_ops o161) (CA.po_ops2 o161) (CA.po_plan o161) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert162 : as0_cut_cert ITR BF cp162 (CA.po_ops o162) (CA.po_ops2 o162) (CA.po_plan o162) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert163 : as0_cut_cert ITR BF cp163 (CA.po_ops o163) (CA.po_ops2 o163) (CA.po_plan o163) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert164 : as0_cut_cert ITR BF cp164 (CA.po_ops o164) (CA.po_ops2 o164) (CA.po_plan o164) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert165 : as0_cut_cert ITR BF cp165 (CA.po_ops o165) (CA.po_ops2 o165) (CA.po_plan o165) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert166 : as0_cut_cert ITR BF cp166 (CA.po_ops o166) (CA.po_ops2 o166) (CA.po_plan o166) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert167 : as0_cut_cert ITR BF cp167 (CA.po_ops o167) (CA.po_ops2 o167) (CA.po_plan o167) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert168 : as0_cut_cert ITR BF cp168 (CA.po_ops o168) (CA.po_ops2 o168) (CA.po_plan o168) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert169 : as0_cut_cert ITR BF cp169 (CA.po_ops o169) (CA.po_ops2 o169) (CA.po_plan o169) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
